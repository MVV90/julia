# This file is a part of Julia. License is MIT: https://julialang.org/license

# Factorials

const _fact_table64 = Vector{Int64}(undef, 20)
_fact_table64[1] = 1
for n in 2:20
    _fact_table64[n] = _fact_table64[n-1] * n
end

const _fact_table128 = Vector{UInt128}(undef, 34)
_fact_table128[1] = 1
for n in 2:34
    _fact_table128[n] = _fact_table128[n-1] * n
end

function factorial_lookup(n::Integer, table, lim)
    n < 0 && throw(DomainError(n, "`n` must not be negative."))
    n > lim && throw(OverflowError(string(n, " is too large to look up in the table; consider using `factorial(UInt128(", n, "))` instead")))
    n == 0 && return one(n)
    @inbounds f = table[n]
    return oftype(n, f)
end

factorial(n::Int128) = factorial_lookup(n, _fact_table128, 33)
factorial(n::UInt128) = factorial_lookup(n, _fact_table128, 34)
factorial(n::Union{Int64,UInt64}) = factorial_lookup(n, _fact_table64, 20)

if Int === Int32
    factorial(n::Union{Int8,UInt8,Int16,UInt16}) = factorial(Int32(n))
    factorial(n::Union{Int32,UInt32}) = factorial_lookup(n, _fact_table64, 12)
else
    factorial(n::Union{Int8,UInt8,Int16,UInt16,Int32,UInt32}) = factorial(Int64(n))
end


# Basic functions for working with permutations

@inline function _foldoneto(op, acc, ::Val{N}) where N
    @assert N::Integer > 0
    if @generated
        quote
            acc_0 = acc
            Base.Cartesian.@nexprs $N i -> acc_{i} = op(acc_{i-1}, i)
            return $(Symbol(:acc_, N))
        end
    else
        for i in 1:N
            acc = op(acc, i)
        end
        return acc
    end
end

"""
    isperm(v) -> Bool

Return `true` if `v` is a valid permutation.

# Examples
```jldoctest
julia> isperm([1; 2])
true

julia> isperm([1; 3])
false
```
"""
isperm(A) = _isperm(A)

function _isperm(A)
    n = length(A)
    used = falses(n)
    for a in A
        (0 < a <= n) && (used[a] ⊻= true) || return false
    end
    true
end

isperm(p::Tuple{}) = true
isperm(p::Tuple{Int}) = p[1] == 1
isperm(p::Tuple{Int,Int}) = ((p[1] == 1) & (p[2] == 2)) | ((p[1] == 2) & (p[2] == 1))

function isperm(P::Tuple)
    valn = Val(length(P))
    _foldoneto(true, valn) do b,i
        s = _foldoneto(false, valn) do s, j
            s || P[j]==i
        end
        b&s
    end
end

isperm(P::Any32) = _isperm(P)

# swap columns i and j of a, in-place
function swapcols!(a::AbstractMatrix, i, j)
    i == j && return
    cols = axes(a,2)
    @boundscheck i in cols || throw(BoundsError(a, (:,i)))
    @boundscheck j in cols || throw(BoundsError(a, (:,j)))
    for k in axes(a,1)
        @inbounds a[k,i],a[k,j] = a[k,j],a[k,i]
    end
end

# swap rows i and j of a, in-place
function swaprows!(a::AbstractMatrix, i, j)
    i == j && return
    rows = axes(a,1)
    @boundscheck i in rows || throw(BoundsError(a, (:,i)))
    @boundscheck j in rows || throw(BoundsError(a, (:,j)))
    for k in axes(a,2)
        @inbounds a[i,k],a[j,k] = a[j,k],a[i,k]
    end
end

# like permute!! applied to each row of a, in-place in a (overwriting p).
function permutecols!!(a::AbstractMatrix, p::AbstractVector{<:Integer})
    require_one_based_indexing(a, p)
    count = 0
    start = 0
    while count < length(p)
        ptr = start = findnext(!iszero, p, start+1)::Int
        next = p[start]
        count += 1
        while next != start
            swapcols!(a, ptr, next)
            p[ptr] = 0
            ptr = next
            next = p[next]
            count += 1
        end
        p[ptr] = 0
    end
    a
end

function permute!!(a, p::AbstractVector{<:Integer})
    require_one_based_indexing(a, p)
    count = 0
    start = 0
    while count < length(a)
        ptr = start = findnext(!iszero, p, start+1)::Int
        temp = a[start]
        next = p[start]
        count += 1
        while next != start
            a[ptr] = a[next]
            p[ptr] = 0
            ptr = next
            next = p[next]
            count += 1
        end
        a[ptr] = temp
        p[ptr] = 0
    end
    a
end

"""
    permute!(v, p)

Permute vector `v` in-place, according to permutation `p`. No checking is done
to verify that `p` is a permutation.

To return a new permutation, use `v[p]`. Note that this is generally faster than
`permute!(v,p)` for large vectors.

See also [`invpermute!`](@ref).

# Examples
```jldoctest
julia> A = [1, 1, 3, 4];

julia> perm = [2, 4, 3, 1];

julia> permute!(A, perm);

julia> A
4-element Vector{Int64}:
 1
 4
 3
 1
```
"""
permute!(a, p::AbstractVector) = permute!!(a, copymutable(p))

function invpermute!!(a, p::AbstractVector{<:Integer})
    require_one_based_indexing(a, p)
    count = 0
    start = 0
    while count < length(a)
        start = findnext(!iszero, p, start+1)::Int
        temp = a[start]
        next = p[start]
        count += 1
        while next != start
            temp_next = a[next]
            a[next] = temp
            temp = temp_next
            ptr = p[next]
            p[next] = 0
            next = ptr
            count += 1
        end
        a[next] = temp
        p[next] = 0
    end
    a
end

"""
    invpermute!(v, p)

Like [`permute!`](@ref), but the inverse of the given permutation is applied.

# Examples
```jldoctest
julia> A = [1, 1, 3, 4];

julia> perm = [2, 4, 3, 1];

julia> invpermute!(A, perm);

julia> A
4-element Vector{Int64}:
 4
 1
 3
 1
```
"""
invpermute!(a, p::AbstractVector) = invpermute!!(a, copymutable(p))

"""
    invperm(v)

Return the inverse permutation of `v`.
If `B = A[v]`, then `A == B[invperm(v)]`.

See also [`sortperm`](@ref), [`invpermute!`](@ref), [`isperm`](@ref), [`permutedims`](@ref).

# Examples
```jldoctest
julia> p = (2, 3, 1);

julia> invperm(p)
(3, 1, 2)

julia> v = [2; 4; 3; 1];

julia> invperm(v)
4-element Vector{Int64}:
 4
 1
 3
 2

julia> A = ['a','b','c','d'];

julia> B = A[v]
4-element Vector{Char}:
 'b': ASCII/Unicode U+0062 (category Ll: Letter, lowercase)
 'd': ASCII/Unicode U+0064 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)

julia> B[invperm(v)]
4-element Vector{Char}:
 'a': ASCII/Unicode U+0061 (category Ll: Letter, lowercase)
 'b': ASCII/Unicode U+0062 (category Ll: Letter, lowercase)
 'c': ASCII/Unicode U+0063 (category Ll: Letter, lowercase)
 'd': ASCII/Unicode U+0064 (category Ll: Letter, lowercase)
```
"""
function invperm(a::AbstractVector)
    require_one_based_indexing(a)
    b = zero(a) # similar vector of zeros
    n = length(a)
    @inbounds for (i, j) in enumerate(a)
        ((1 <= j <= n) && b[j] == 0) ||
            throw(ArgumentError("argument is not a permutation"))
        b[j] = i
    end
    b
end

function invperm(p::Union{Tuple{},Tuple{Int},Tuple{Int,Int}})
    isperm(p) || throw(ArgumentError("argument is not a permutation"))
    p  # in dimensions 0-2, every permutation is its own inverse
end

function invperm(P::Tuple)
    valn = Val(length(P))
    ntuple(valn) do i
        s = _foldoneto(nothing, valn) do s, j
            s !== nothing && return s
            P[j]==i && return j
            nothing
        end
        s === nothing && throw(ArgumentError("argument is not a permutation"))
        s
    end
end

invperm(P::Any32) = Tuple(invperm(collect(P)))

#XXX This function should be moved to Combinatorics.jl but is currently used by Base.DSP.
"""
    nextprod(factors::Union{Tuple,AbstractVector}, n)

Next integer greater than or equal to `n` that can be written as ``\\prod k_i^{p_i}`` for integers
``p_1``, ``p_2``, etcetera, for factors ``k_i`` in `factors`.

# Examples
```jldoctest
julia> nextprod((2, 3), 105)
108

julia> 2^2 * 3^3
108
```

!!! compat "Julia 1.6"
    The method that accepts a tuple requires Julia 1.6 or later.
"""
function nextprod(a::Union{Tuple{Vararg{Integer}},AbstractVector{<:Integer}}, x::Real)
    if x > typemax(Int)
        throw(ArgumentError("unsafe for x > typemax(Int), got $x"))
    end
    k = length(a)
    v = fill(1, k)                    # current value of each counter
    mx = map(a -> nextpow(a,x), a)   # maximum value of each counter
    v[1] = mx[1]                      # start at first case that is >= x
    p::widen(Int) = mx[1]             # initial value of product in this case
    best = p
    icarry = 1

    while v[end] < mx[end]
        if p >= x
            best = p < best ? p : best  # keep the best found yet
            carrytest = true
            while carrytest
                p = div(p, v[icarry])
                v[icarry] = 1
                icarry += 1
                p *= a[icarry]
                v[icarry] *= a[icarry]
                carrytest = v[icarry] > mx[icarry] && icarry < k
            end
            if p < x
                icarry = 1
            end
        else
            while p < x
                p *= a[1]
                v[1] *= a[1]
            end
        end
    end
    # might overflow, but want predictable return type
    return mx[end] < best ? Int(mx[end]) : Int(best)
end
