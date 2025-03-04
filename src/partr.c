// This file is a part of Julia. License is MIT: https://julialang.org/license

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>

#include "julia.h"
#include "julia_internal.h"
#include "gc.h"
#include "threading.h"

#ifdef __cplusplus
extern "C" {
#endif


// thread sleep state

// default to DEFAULT_THREAD_SLEEP_THRESHOLD; set via $JULIA_THREAD_SLEEP_THRESHOLD
uint64_t sleep_threshold;

// thread should not be sleeping--it might need to do work.
static const int16_t not_sleeping = 0;

// it is acceptable for the thread to be sleeping.
static const int16_t sleeping = 1;

// invariant: No thread is ever asleep unless sleep_check_state is sleeping (or we have a wakeup signal pending).
// invariant: Any particular thread is not asleep unless that thread's sleep_check_state is sleeping.
// invariant: The transition of a thread state to sleeping must be followed by a check that there wasn't work pending for it.
// information: Observing thread not-sleeping is sufficient to ensure the target thread will subsequently inspect its local queue.
// information: Observing thread is-sleeping says it may be necessary to notify it at least once to wakeup. It may already be awake however for a variety of reasons.
// information: These observations require sequentially-consistent fences to be inserted between each of those operational phases.
// [^store_buffering_1]: These fences are used to avoid the cycle 2b -> 1a -> 1b -> 2a -> 2b where
// * Dequeuer:
//   * 1a: `jl_atomic_store_relaxed(&ptls->sleep_check_state, sleeping)`
//   * 1b: `multiq_check_empty` returns true
// * Enqueuer:
//   * 2a: `multiq_insert`
//   * 2b: `jl_atomic_load_relaxed(&ptls->sleep_check_state)` in `jl_wakeup_thread` returns `not_sleeping`
// i.e., the dequeuer misses the enqueue and enqueuer misses the sleep state transition.
// [^store_buffering_2]: and also
// * Enqueuer:
//   * 1a: `jl_atomic_store_relaxed(jl_uv_n_waiters, 1)` in `JL_UV_LOCK`
//   * 1b: "cheap read" of `handle->pending` in `uv_async_send` (via `JL_UV_LOCK`) loads `0`
// * Dequeuer:
//   * 2a: store `2` to `handle->pending` in `uv_async_send` (via `JL_UV_LOCK` in `jl_task_get_next`)
//   * 2b: `jl_atomic_load_relaxed(jl_uv_n_waiters)` in `jl_task_get_next` returns `0`
// i.e., the dequeuer misses the `n_waiters` is set and enqueuer misses the `uv_stop` flag (in `signal_async`) transition to cleared

JULIA_DEBUG_SLEEPWAKE(
uint64_t wakeup_enter;
uint64_t wakeup_leave;
uint64_t io_wakeup_enter;
uint64_t io_wakeup_leave;
);

uv_mutex_t *sleep_locks;
uv_cond_t *wake_signals;

JL_DLLEXPORT int jl_set_task_tid(jl_task_t *task, int tid) JL_NOTSAFEPOINT
{
    // Try to acquire the lock on this task.
    int16_t was = jl_atomic_load_relaxed(&task->tid);
    if (was == tid)
        return 1;
    if (was == -1)
        return jl_atomic_cmpswap(&task->tid, &was, tid);
    return 0;
}

// GC functions used
extern int jl_gc_mark_queue_obj_explicit(jl_gc_mark_cache_t *gc_cache,
                                         jl_gc_mark_sp_t *sp, jl_value_t *obj) JL_NOTSAFEPOINT;

// multiq
// ---

/* a task heap */
typedef struct taskheap_tag {
    uv_mutex_t lock;
    jl_task_t **tasks;
    _Atomic(int32_t) ntasks;
    _Atomic(int16_t) prio;
} taskheap_t;

/* multiqueue parameters */
static const int32_t heap_d = 8;
static const int heap_c = 2;

/* size of each heap */
static const int tasks_per_heap = 65536; // TODO: this should be smaller by default, but growable!

/* the multiqueue's heaps */
static taskheap_t *heaps;
static int32_t heap_p;

/* unbias state for the RNG */
static uint64_t cong_unbias;


static inline void multiq_init(void)
{
    heap_p = heap_c * jl_n_threads;
    heaps = (taskheap_t *)calloc(heap_p, sizeof(taskheap_t));
    for (int32_t i = 0; i < heap_p; ++i) {
        uv_mutex_init(&heaps[i].lock);
        heaps[i].tasks = (jl_task_t **)calloc(tasks_per_heap, sizeof(jl_task_t*));
        jl_atomic_store_relaxed(&heaps[i].ntasks, 0);
        jl_atomic_store_relaxed(&heaps[i].prio, INT16_MAX);
    }
    unbias_cong(heap_p, &cong_unbias);
}


static inline void sift_up(taskheap_t *heap, int32_t idx)
{
    if (idx > 0) {
        int32_t parent = (idx-1)/heap_d;
        if (heap->tasks[idx]->prio < heap->tasks[parent]->prio) {
            jl_task_t *t = heap->tasks[parent];
            heap->tasks[parent] = heap->tasks[idx];
            heap->tasks[idx] = t;
            sift_up(heap, parent);
        }
    }
}


static inline void sift_down(taskheap_t *heap, int32_t idx)
{
    if (idx < jl_atomic_load_relaxed(&heap->ntasks)) {
        for (int32_t child = heap_d*idx + 1;
                child < tasks_per_heap && child <= heap_d*idx + heap_d;
                ++child) {
            if (heap->tasks[child]
                    && heap->tasks[child]->prio < heap->tasks[idx]->prio) {
                jl_task_t *t = heap->tasks[idx];
                heap->tasks[idx] = heap->tasks[child];
                heap->tasks[child] = t;
                sift_down(heap, child);
            }
        }
    }
}


static inline int multiq_insert(jl_task_t *task, int16_t priority)
{
    jl_ptls_t ptls = jl_current_task->ptls;
    uint64_t rn;

    task->prio = priority;
    do {
        rn = cong(heap_p, cong_unbias, &ptls->rngseed);
    } while (uv_mutex_trylock(&heaps[rn].lock) != 0);

    if (jl_atomic_load_relaxed(&heaps[rn].ntasks) >= tasks_per_heap) {
        uv_mutex_unlock(&heaps[rn].lock);
        // multiq insertion failed, increase #tasks per heap
        return -1;
    }

    int32_t ntasks = jl_atomic_load_relaxed(&heaps[rn].ntasks);
    jl_atomic_store_relaxed(&heaps[rn].ntasks, ntasks + 1);
    heaps[rn].tasks[ntasks] = task;
    sift_up(&heaps[rn], ntasks);
    int16_t prio = jl_atomic_load_relaxed(&heaps[rn].prio);
    if (task->prio < prio)
        jl_atomic_store_relaxed(&heaps[rn].prio, task->prio);
    uv_mutex_unlock(&heaps[rn].lock);

    return 0;
}


static inline jl_task_t *multiq_deletemin(void)
{
    jl_ptls_t ptls = jl_current_task->ptls;
    uint64_t rn1 = 0, rn2;
    int32_t i;
    int16_t prio1, prio2;
    jl_task_t *task;
 retry:
    jl_gc_safepoint();
    for (i = 0; i < heap_p; ++i) {
        rn1 = cong(heap_p, cong_unbias, &ptls->rngseed);
        rn2 = cong(heap_p, cong_unbias, &ptls->rngseed);
        prio1 = jl_atomic_load_relaxed(&heaps[rn1].prio);
        prio2 = jl_atomic_load_relaxed(&heaps[rn2].prio);
        if (prio1 > prio2) {
            prio1 = prio2;
            rn1 = rn2;
        }
        else if (prio1 == prio2 && prio1 == INT16_MAX)
            continue;
        if (uv_mutex_trylock(&heaps[rn1].lock) == 0) {
            if (prio1 == jl_atomic_load_relaxed(&heaps[rn1].prio))
                break;
            uv_mutex_unlock(&heaps[rn1].lock);
        }
    }
    if (i == heap_p)
        return NULL;

    task = heaps[rn1].tasks[0];
    if (!jl_set_task_tid(task, ptls->tid)) {
        uv_mutex_unlock(&heaps[rn1].lock);
        goto retry;
    }
    int32_t ntasks = jl_atomic_load_relaxed(&heaps[rn1].ntasks) - 1;
    jl_atomic_store_relaxed(&heaps[rn1].ntasks, ntasks);
    heaps[rn1].tasks[0] = heaps[rn1].tasks[ntasks];
    heaps[rn1].tasks[ntasks] = NULL;
    prio1 = INT16_MAX;
    if (ntasks > 0) {
        sift_down(&heaps[rn1], 0);
        prio1 = heaps[rn1].tasks[0]->prio;
    }
    jl_atomic_store_relaxed(&heaps[rn1].prio, prio1);
    uv_mutex_unlock(&heaps[rn1].lock);

    return task;
}


void jl_gc_mark_enqueued_tasks(jl_gc_mark_cache_t *gc_cache, jl_gc_mark_sp_t *sp)
{
    int32_t i, j;
    for (i = 0; i < heap_p; ++i)
        for (j = 0; j < jl_atomic_load_relaxed(&heaps[i].ntasks); ++j)
            jl_gc_mark_queue_obj_explicit(gc_cache, sp, (jl_value_t *)heaps[i].tasks[j]);
}


static int multiq_check_empty(void)
{
    int32_t i;
    for (i = 0; i < heap_p; ++i) {
        if (jl_atomic_load_relaxed(&heaps[i].ntasks) != 0)
            return 0;
    }
    return 1;
}



// parallel task runtime
// ---

// initialize the threading infrastructure
// (used only by the main thread)
void jl_init_threadinginfra(void)
{
    /* initialize the synchronization trees pool and the multiqueue */
    multiq_init();

    sleep_threshold = DEFAULT_THREAD_SLEEP_THRESHOLD;
    char *cp = getenv(THREAD_SLEEP_THRESHOLD_NAME);
    if (cp) {
        if (!strncasecmp(cp, "infinite", 8))
            sleep_threshold = UINT64_MAX;
        else
            sleep_threshold = (uint64_t)strtol(cp, NULL, 10);
    }

    jl_ptls_t ptls = jl_current_task->ptls;
    jl_install_thread_signal_handler(ptls);

    int16_t tid;
    sleep_locks = (uv_mutex_t*)calloc(jl_n_threads, sizeof(uv_mutex_t));
    wake_signals = (uv_cond_t*)calloc(jl_n_threads, sizeof(uv_cond_t));
    for (tid = 0; tid < jl_n_threads; tid++) {
        uv_mutex_init(&sleep_locks[tid]);
        uv_cond_init(&wake_signals[tid]);
    }
}


void JL_NORETURN jl_finish_task(jl_task_t *t);

// thread function: used by all except the main thread
void jl_threadfun(void *arg)
{
    jl_threadarg_t *targ = (jl_threadarg_t*)arg;

    // initialize this thread (set tid, create heap, set up root task)
    jl_ptls_t ptls = jl_init_threadtls(targ->tid);
    void *stack_lo, *stack_hi;
    jl_init_stack_limits(0, &stack_lo, &stack_hi);
    // warning: this changes `jl_current_task`, so be careful not to call that from this function
    jl_task_t *ct = jl_init_root_task(ptls, stack_lo, stack_hi);
    JL_GC_PROMISE_ROOTED(ct);
    jl_install_thread_signal_handler(ptls);

    // wait for all threads
    jl_gc_state_set(ptls, JL_GC_STATE_SAFE, 0);
    uv_barrier_wait(targ->barrier);

    // free the thread argument here
    free(targ);

    (void)jl_gc_unsafe_enter(ptls);
    jl_finish_task(ct); // noreturn
}


// enqueue the specified task for execution
JL_DLLEXPORT int jl_enqueue_task(jl_task_t *task)
{
    char failed;
    if (multiq_insert(task, task->prio) == -1)
        failed = 1;
    failed = 0;
    JL_PROBE_RT_TASKQ_INSERT(jl_current_task->ptls, task);
    return failed;
}


int jl_running_under_rr(int recheck)
{
#ifdef _OS_LINUX_
#define RR_CALL_BASE 1000
#define SYS_rrcall_check_presence (RR_CALL_BASE + 8)
    static _Atomic(int) is_running_under_rr = 0;
    int rr = jl_atomic_load_relaxed(&is_running_under_rr);
    if (rr == 0 || recheck) {
        int ret = syscall(SYS_rrcall_check_presence, 0, 0, 0, 0, 0, 0);
        if (ret == -1)
            // Should always be ENOSYS, but who knows what people do for
            // unknown syscalls with their seccomp filters, so just say
            // that we don't have rr.
            rr = 2;
        else
            rr = 1;
        jl_atomic_store_relaxed(&is_running_under_rr, rr);
    }
    return rr == 1;
#else
    return 0;
#endif
}


//  sleep_check_after_threshold() -- if sleep_threshold ns have passed, return 1
static int sleep_check_after_threshold(uint64_t *start_cycles)
{
    JULIA_DEBUG_SLEEPWAKE( return 1 ); // hammer on the sleep/wake logic much harder
    /**
     * This wait loop is a bit of a worst case for rr - it needs timer access,
     * which are slow and it busy loops in user space, which prevents the
     * scheduling logic from switching to other threads. Just don't bother
     * trying to wait here
     */
    if (jl_running_under_rr(0))
        return 1;
    if (!(*start_cycles)) {
        *start_cycles = jl_hrtime();
        return 0;
    }
    uint64_t elapsed_cycles = jl_hrtime() - (*start_cycles);
    if (elapsed_cycles >= sleep_threshold) {
        *start_cycles = 0;
        return 1;
    }
    return 0;
}


static int wake_thread(int16_t tid)
{
    jl_ptls_t other = jl_all_tls_states[tid];
    int8_t state = sleeping;

    if (jl_atomic_load_relaxed(&other->sleep_check_state) == sleeping) {
        if (jl_atomic_cmpswap_relaxed(&other->sleep_check_state, &state, not_sleeping)) {
            JL_PROBE_RT_SLEEP_CHECK_WAKE(other, state);
            uv_mutex_lock(&sleep_locks[tid]);
            uv_cond_signal(&wake_signals[tid]);
            uv_mutex_unlock(&sleep_locks[tid]);
            return 1;
        }
    }
    return 0;
}


static void wake_libuv(void)
{
    JULIA_DEBUG_SLEEPWAKE( io_wakeup_enter = cycleclock() );
    jl_wake_libuv();
    JULIA_DEBUG_SLEEPWAKE( io_wakeup_leave = cycleclock() );
}

/* ensure thread tid is awake if necessary */
JL_DLLEXPORT void jl_wakeup_thread(int16_t tid)
{
    jl_task_t *ct = jl_current_task;
    int16_t self = jl_atomic_load_relaxed(&ct->tid);
    if (tid != self)
        jl_fence(); // [^store_buffering_1]
    jl_task_t *uvlock = jl_atomic_load_relaxed(&jl_uv_mutex.owner);
    JULIA_DEBUG_SLEEPWAKE( wakeup_enter = cycleclock() );
    if (tid == self || tid == -1) {
        // we're already awake, but make sure we'll exit uv_run
        jl_ptls_t ptls = ct->ptls;
        if (jl_atomic_load_relaxed(&ptls->sleep_check_state) == sleeping) {
            jl_atomic_store_relaxed(&ptls->sleep_check_state, not_sleeping);
            JL_PROBE_RT_SLEEP_CHECK_WAKEUP(ptls);
        }
        if (uvlock == ct)
            uv_stop(jl_global_event_loop());
    }
    else {
        // something added to the sticky-queue: notify that thread
        if (wake_thread(tid)) {
            // check if we need to notify uv_run too
            jl_fence();
            jl_task_t *tid_task = jl_atomic_load_relaxed(&jl_all_tls_states[tid]->current_task);
            // now that we have changed the thread to not-sleeping, ensure that
            // either it has not yet acquired the libuv lock, or that it will
            // observe the change of state to not_sleeping
            if (uvlock != ct && jl_atomic_load_relaxed(&jl_uv_mutex.owner) == tid_task)
                wake_libuv();
        }
    }
    // check if the other threads might be sleeping
    if (tid == -1) {
        // something added to the multi-queue: notify all threads
        // in the future, we might want to instead wake some fraction of threads,
        // and let each of those wake additional threads if they find work
        int anysleep = 0;
        for (tid = 0; tid < jl_n_threads; tid++) {
            if (tid != self)
                anysleep |= wake_thread(tid);
        }
        // check if we need to notify uv_run too
        if (uvlock != ct && anysleep) {
            jl_fence();
            if (jl_atomic_load_relaxed(&jl_uv_mutex.owner) != NULL)
                wake_libuv();
        }
    }
    JULIA_DEBUG_SLEEPWAKE( wakeup_leave = cycleclock() );
}


// get the next runnable task from the multiq
static jl_task_t *get_next_task(jl_value_t *trypoptask, jl_value_t *q)
{
    jl_gc_safepoint();
    jl_value_t *args[2] = { trypoptask, q };
    jl_task_t *task = (jl_task_t*)jl_apply(args, 2);
    if (jl_typeis(task, jl_task_type)) {
        int self = jl_atomic_load_relaxed(&jl_current_task->tid);
        jl_set_task_tid(task, self);
        return task;
    }
    task = multiq_deletemin();
    if (task)
        JL_PROBE_RT_TASKQ_GET(jl_current_task->ptls, task);
    return task;
}

static int may_sleep(jl_ptls_t ptls) JL_NOTSAFEPOINT
{
    // sleep_check_state is only transitioned from not_sleeping to sleeping
    // by the thread itself. As a result, if this returns false, it will
    // continue returning false. If it returns true, we know the total
    // modification order of the fences.
    jl_fence(); // [^store_buffering_1] [^store_buffering_2]
    return jl_atomic_load_relaxed(&ptls->sleep_check_state) == sleeping;
}

extern _Atomic(unsigned) _threadedregion;

JL_DLLEXPORT jl_task_t *jl_task_get_next(jl_value_t *trypoptask, jl_value_t *q)
{
    jl_task_t *ct = jl_current_task;
    uint64_t start_cycles = 0;

    while (1) {
        jl_task_t *task = get_next_task(trypoptask, q);
        if (task)
            return task;

        // quick, race-y check to see if there seems to be any stuff in there
        jl_cpu_pause();
        if (!multiq_check_empty()) {
            start_cycles = 0;
            continue;
        }

        jl_cpu_pause();
        jl_ptls_t ptls = ct->ptls;
        if (sleep_check_after_threshold(&start_cycles) || (!jl_atomic_load_relaxed(&_threadedregion) && ptls->tid == 0)) {
            // acquire sleep-check lock
            jl_atomic_store_relaxed(&ptls->sleep_check_state, sleeping);
            jl_fence(); // [^store_buffering_1]
            JL_PROBE_RT_SLEEP_CHECK_SLEEP(ptls);
            if (!multiq_check_empty()) { // uses relaxed loads
                if (jl_atomic_load_relaxed(&ptls->sleep_check_state) != not_sleeping) {
                    jl_atomic_store_relaxed(&ptls->sleep_check_state, not_sleeping); // let other threads know they don't need to wake us
                    JL_PROBE_RT_SLEEP_CHECK_TASKQ_WAKE(ptls);
                }
                continue;
            }
            task = get_next_task(trypoptask, q); // note: this should not yield
            if (ptls != ct->ptls) {
                // sigh, a yield was detected, so let's go ahead and handle it anyway by starting over
                ptls = ct->ptls;
                if (jl_atomic_load_relaxed(&ptls->sleep_check_state) != not_sleeping) {
                    jl_atomic_store_relaxed(&ptls->sleep_check_state, not_sleeping); // let other threads know they don't need to wake us
                    JL_PROBE_RT_SLEEP_CHECK_TASK_WAKE(ptls);
                }
                if (task)
                    return task;
                continue;
            }
            if (task) {
                if (jl_atomic_load_relaxed(&ptls->sleep_check_state) != not_sleeping) {
                    jl_atomic_store_relaxed(&ptls->sleep_check_state, not_sleeping); // let other threads know they don't need to wake us
                    JL_PROBE_RT_SLEEP_CHECK_TASK_WAKE(ptls);
                }
                return task;
            }


            // IO is always permitted, but outside a threaded region, only
            // thread 0 will process messages.
            // Inside a threaded region, any thread can listen for IO messages,
            // and one thread should win this race and watch the event loop,
            // but we bias away from idle threads getting parked here.
            //
            // The reason this works is somewhat convoluted, and closely tied to [^store_buffering_1]:
            //  - After decrementing _threadedregion, the thread is required to
            //    call jl_wakeup_thread(0), that will kick out any thread who is
            //    already there, and then eventually thread 0 will get here.
            //  - Inside a _threadedregion, there must exist at least one
            //    thread that has a happens-before relationship on the libuv lock
            //    before reaching this decision point in the code who will see
            //    the lock as unlocked and thus must win this race here.
            int uvlock = 0;
            if (jl_atomic_load_relaxed(&_threadedregion)) {
                uvlock = jl_mutex_trylock(&jl_uv_mutex);
            }
            else if (ptls->tid == 0) {
                uvlock = 1;
                JL_UV_LOCK(); // jl_mutex_lock(&jl_uv_mutex);
            }
            if (uvlock) {
                int active = 1;
                // otherwise, we block until someone asks us for the lock
                uv_loop_t *loop = jl_global_event_loop();
                while (active && may_sleep(ptls)) {
                    if (jl_atomic_load_relaxed(&jl_uv_n_waiters) != 0)
                        // but if we won the race against someone who actually needs
                        // the lock to do real work, we need to let them have it instead
                        break;
                    loop->stop_flag = 0;
                    JULIA_DEBUG_SLEEPWAKE( ptls->uv_run_enter = cycleclock() );
                    active = uv_run(loop, UV_RUN_ONCE);
                    JULIA_DEBUG_SLEEPWAKE( ptls->uv_run_leave = cycleclock() );
                    jl_gc_safepoint();
                }
                JL_UV_UNLOCK();
                // optimization: check again first if we may have work to do.
                // Otherwise we got a spurious wakeup since some other thread
                // that just wanted to steal libuv from us. We will just go
                // right back to sleep on the individual wake signal to let
                // them take it from us without conflict.
                if (!may_sleep(ptls)) {
                    start_cycles = 0;
                    continue;
                }
                if (!jl_atomic_load_relaxed(&_threadedregion) && active && ptls->tid == 0) {
                    // thread 0 is the only thread permitted to run the event loop
                    // so it needs to stay alive, just spin-looping if necessary
                    if (jl_atomic_load_relaxed(&ptls->sleep_check_state) != not_sleeping) {
                        jl_atomic_store_relaxed(&ptls->sleep_check_state, not_sleeping); // let other threads know they don't need to wake us
                        JL_PROBE_RT_SLEEP_CHECK_UV_WAKE(ptls);
                    }
                    start_cycles = 0;
                    continue;
                }
            }

            // the other threads will just wait for an individual wake signal to resume
            JULIA_DEBUG_SLEEPWAKE( ptls->sleep_enter = cycleclock() );
            int8_t gc_state = jl_gc_safe_enter(ptls);
            uv_mutex_lock(&sleep_locks[ptls->tid]);
            while (may_sleep(ptls)) {
                uv_cond_wait(&wake_signals[ptls->tid], &sleep_locks[ptls->tid]);
                // TODO: help with gc work here, if applicable
            }
            assert(jl_atomic_load_relaxed(&ptls->sleep_check_state) == not_sleeping);
            uv_mutex_unlock(&sleep_locks[ptls->tid]);
            JULIA_DEBUG_SLEEPWAKE( ptls->sleep_leave = cycleclock() );
            jl_gc_safe_leave(ptls, gc_state); // contains jl_gc_safepoint
            start_cycles = 0;
        }
        else {
            // maybe check the kernel for new messages too
            jl_process_events();
        }
    }
}

#ifdef __cplusplus
}
#endif
