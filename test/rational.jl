# This file is a part of Julia. License is MIT: https://julialang.org/license

using Test

@testset "Rationals" begin
    @test 1//1 == 1
    @test 2//2 == 1
    @test 1//1 == 1//1
    @test 2//2 == 1//1
    @test 2//4 == 3//6
    @test 1//2 + 1//2 == 1
    @test (-1)//3 == -(1//3)
    @test 1//2 + 3//4 == 5//4
    @test 1//3 * 3//4 == 1//4
    @test 1//2 / 3//4 == 2//3
    @test 1//0 == 1//0
    @test 5//0 == 1//0
    @test -1//0 == -1//0
    @test -7//0 == -1//0
    @test  (-1//2) // (-2//5) == 5//4

    @test_throws OverflowError -(0x01//0x0f)
    @test_throws OverflowError -(typemin(Int)//1)
    @test_throws OverflowError (typemax(Int)//3) + 1
    @test_throws OverflowError (typemax(Int)//3) * 2
    @test (typemax(Int)//1) * (1//typemax(Int)) == 1
    @test (typemax(Int)//1) / (typemax(Int)//1) == 1
    @test (1//typemax(Int)) / (1//typemax(Int)) == 1
    @test_throws OverflowError (1//2)^63
    @test inv((1+typemin(Int))//typemax(Int)) == -1
    @test_throws ArgumentError inv(typemin(Int)//typemax(Int))
    @test_throws ArgumentError Rational(0x1, typemin(Int32))

    @test @inferred(rationalize(Int, 3.0, 0.0)) === 3//1
    @test @inferred(rationalize(Int, 3.0, 0)) === 3//1
    @test_throws OverflowError rationalize(UInt, -2.0)
    @test_throws ArgumentError rationalize(Int, Float64(3.0), -1.)
    # issue 26823
    @test_throws InexactError rationalize(Int, NaN)
    # issue 32569
    @test_throws ArgumentError 1 // typemin(Int)
    @test_throws ArgumentError 0 // 0
    @test -2 // typemin(Int) == -1 // (typemin(Int) >> 1)
    @test 2 // typemin(Int) == 1 // (typemin(Int) >> 1)

    @test_throws InexactError Rational(UInt(1), typemin(Int32))
    @test iszero(Rational{Int}(UInt(0), 1))
    @test_broken Rational{Int64}(UInt(1), typemin(Int32)) == Int64(1) // Int64(typemin(Int32))

    for a = -5:5, b = -5:5
        if a == b == 0; continue; end
        if ispow2(b)
            @test a//b == a/b
            @test convert(Rational,a/b) == a//b
        end
        @test rationalize(a/b) == a//b
        @test a//b == a//b
        if b == 0
            @test_throws DivideError round(Integer,a//b) == round(Integer,a/b)
        else
            @test round(Integer,a//b) == round(Integer,a/b)
        end
        for c = -5:5
            @test (a//b == c) == (a/b == c)
            @test (a//b != c) == (a/b != c)
            @test (a//b <= c) == (a/b <= c)
            @test (a//b <  c) == (a/b <  c)
            @test (a//b >= c) == (a/b >= c)
            @test (a//b >  c) == (a/b >  c)
            for d = -5:5
                if c == d == 0; continue; end
                @test (a//b == c//d) == (a/b == c/d)
                @test (a//b != c//d) == (a/b != c/d)
                @test (a//b <= c//d) == (a/b <= c/d)
                @test (a//b <  c//d) == (a/b <  c/d)
                @test (a//b >= c//d) == (a/b >= c/d)
                @test (a//b >  c//d) == (a/b >  c/d)
            end
        end
    end

    @test 0.5 == 1//2
    @test 0.1 != 1//10
    @test 0.1 == 3602879701896397//36028797018963968
    @test Inf == 1//0 == 2//0 == typemax(Int)//0
    @test -Inf == -1//0 == -2//0 == -typemax(Int)//0

    @test 1/3 < 1//3
    @test !(1//3 < 1/3)
    @test -1/3 < 1//3
    @test -1/3 > -1//3
    @test 1/3 > -1//3
    @test 1/5 > 1//5
    @test 1//3 < Inf
    @test 0//1 < Inf
    @test 1//0 == Inf
    @test -1//0 == -Inf
    @test -1//0 != Inf
    @test 1//0 != -Inf
    @test !(1//0 < Inf)
    @test !(1//3 < NaN)
    @test !(1//3 == NaN)
    @test !(1//3 > NaN)

    # PR 29561
    @test abs(one(Rational{UInt})) === one(Rational{UInt})
    @test abs(one(Rational{Int})) === one(Rational{Int})
    @test abs(-one(Rational{Int})) === one(Rational{Int})

    # inf addition
    @test 1//0 + 1//0 == 1//0
    @test -1//0 - 1//0 == -1//0
    @test_throws DivideError 1//0 - 1//0
    @test_throws DivideError -1//0 + 1//0
    @test Int128(1)//0 + 1//0 isa Rational{Int128}
    @test 1//0 + Int128(1)//0 isa Rational{Int128}
end

@testset "Rational methods" begin
    rand_int = rand(Int8)

    for T in [Int8, Int16, Int32, Int128]
        @test numerator(convert(T, rand_int)) == rand_int
        @test denominator(convert(T, rand_int)) == 1

        @test typemin(Rational{T}) == -one(T)//zero(T)
        @test typemax(Rational{T}) == one(T)//zero(T)
        @test widen(Rational{T}) == Rational{widen(T)}
    end

    @test iszero(typemin(Rational{UInt}))

    @test Rational(Float32(rand_int)) == Rational(rand_int)

    @test Rational(Rational(rand_int)) == Rational(rand_int)

    @test begin
        var = -Rational(UInt32(0))
        var == UInt32(0)
    end

    @test Rational(rand_int, 3)/Complex(3, 2) == Complex(Rational(rand_int, 13), -Rational(rand_int*2, 39))

    @test Complex(rand_int, 0) == Rational(rand_int)
    @test Rational(rand_int) == Complex(rand_int, 0)

    @test (Complex(rand_int, 4) == Rational(rand_int)) == false
    @test (Rational(rand_int) == Complex(rand_int, 4)) == false

    for a = -3:3
        @test Rational(Float32(a)) == Rational(a)
        @test Rational(a)//2 == a//2
        @test a//Rational(2) == Rational(a/2)
        @test a.//[-2, -1, 1, 2] == [-a//2, -a//1, a//1, a//2]
        for b=-3:3, c=1:3
            @test b//(a+c*im) == b*a//(a^2+c^2)-(b*c//(a^2+c^2))*im
            for d=-3:3
                @test (a+b*im)//(c+d*im) == (a*c+b*d+(b*c-a*d)*im)//(c^2+d^2)
                @test Complex(Rational(a)+b*im)//Complex(Rational(c)+d*im) == Complex(a+b*im)//Complex(c+d*im)
            end
        end
    end
end

# check type of constructed rationals
int_types = Base.BitInteger64_types
for N = int_types, D = int_types
    T = promote_type(N,D)
    @test typeof(convert(N,2)//convert(D,3)) <: Rational{T}
end

# issue #7564
@test typeof(convert(Rational{Integer},1)) === Rational{Integer}

@testset "show and Rationals" begin
    io = IOBuffer()
    rational1 = Rational(1465, 8593)
    rational2 = Rational(-4500, 9000)
    @test sprint(show, rational1) == "1465//8593"
    @test sprint(show, rational2) == "-1//2"
    let
        io1 = IOBuffer()
        write(io1, rational1)
        io1.ptr = 1
        @test read(io1, typeof(rational1)) == rational1

        io2 = IOBuffer()
        write(io2, rational2)
        io2.ptr = 1
        @test read(io2, typeof(rational2)) == rational2
    end
end

@testset "round" begin
    @test round(11//2) == round(11//2, RoundNearest) == 6//1 # rounds to closest _even_ integer
    @test round(-11//2) == round(-11//2, RoundNearest) == -6//1 # rounds to closest _even_ integer
    @test round(13//2) == round(13//2, RoundNearest) == 6//1 # rounds to closest _even_ integer
    @test round(-13//2) == round(-13//2, RoundNearest) == -6//1 # rounds to closest _even_ integer
    @test round(11//3) == round(11//3, RoundNearest) == 4//1 # rounds to closest _even_ integer
    @test round(-11//3) == round(-11//3, RoundNearest) == -4//1 # rounds to closest _even_ integer

    @test round(11//2, RoundNearestTiesAway) == 6//1
    @test round(-11//2, RoundNearestTiesAway) == -6//1
    @test round(13//2, RoundNearestTiesAway) == 7//1
    @test round(-13//2, RoundNearestTiesAway) == -7//1
    @test round(11//3, RoundNearestTiesAway) == 4//1
    @test round(-11//3, RoundNearestTiesAway) == -4//1

    @test round(11//2, RoundNearestTiesUp) == 6//1
    @test round(-11//2, RoundNearestTiesUp) == -5//1
    @test round(13//2, RoundNearestTiesUp) == 7//1
    @test round(-13//2, RoundNearestTiesUp) == -6//1
    @test round(11//3, RoundNearestTiesUp) == 4//1
    @test round(-11//3, RoundNearestTiesUp) == -4//1

    @test trunc(11//2) == round(11//2, RoundToZero) == 5//1
    @test trunc(-11//2) == round(-11//2, RoundToZero) == -5//1
    @test trunc(13//2) == round(13//2, RoundToZero) == 6//1
    @test trunc(-13//2) == round(-13//2, RoundToZero) == -6//1
    @test trunc(11//3) == round(11//3, RoundToZero) == 3//1
    @test trunc(-11//3) == round(-11//3, RoundToZero) == -3//1

    @test ceil(11//2) == round(11//2, RoundUp) == 6//1
    @test ceil(-11//2) == round(-11//2, RoundUp) == -5//1
    @test ceil(13//2) == round(13//2, RoundUp) == 7//1
    @test ceil(-13//2) == round(-13//2, RoundUp) == -6//1
    @test ceil(11//3) == round(11//3, RoundUp) == 4//1
    @test ceil(-11//3) == round(-11//3, RoundUp) == -3//1

    @test floor(11//2) == round(11//2, RoundDown) == 5//1
    @test floor(-11//2) == round(-11//2, RoundDown) == -6//1
    @test floor(13//2) == round(13//2, RoundDown) == 6//1
    @test floor(-13//2) == round(-13//2, RoundDown) == -7//1
    @test floor(11//3) == round(11//3, RoundDown) == 3//1
    @test floor(-11//3) == round(-11//3, RoundDown) == -4//1

    for T in (Float16, Float32, Float64)
        @test round(T, true//false) === convert(T, Inf)
        @test round(T, true//true) === one(T)
        @test round(T, false//true) === zero(T)
        @test trunc(T, true//false) === convert(T, Inf)
        @test trunc(T, true//true) === one(T)
        @test trunc(T, false//true) === zero(T)
        @test floor(T, true//false) === convert(T, Inf)
        @test floor(T, true//true) === one(T)
        @test floor(T, false//true) === zero(T)
        @test ceil(T, true//false) === convert(T, Inf)
        @test ceil(T, true//true) === one(T)
        @test ceil(T, false//true) === zero(T)
    end

    for T in (Int8, Int16, Int32, Int64, Bool)
        @test_throws DivideError round(T, true//false)
        @test round(T, true//true) === one(T)
        @test round(T, false//true) === zero(T)
        @test_throws DivideError trunc(T, true//false)
        @test trunc(T, true//true) === one(T)
        @test trunc(T, false//true) === zero(T)
        @test_throws DivideError floor(T, true//false)
        @test floor(T, true//true) === one(T)
        @test floor(T, false//true) === zero(T)
        @test_throws DivideError ceil(T, true//false)
        @test ceil(T, true//true) === one(T)
        @test ceil(T, false//true) === zero(T)
    end

    # issue 34657
    @test round(1//0) === round(Rational, 1//0) === 1//0
    @test trunc(1//0) === trunc(Rational, 1//0) === 1//0
    @test floor(1//0) === floor(Rational, 1//0) === 1//0
    @test ceil(1//0) === ceil(Rational, 1//0) === 1//0
    @test round(-1//0) === round(Rational, -1//0) === -1//0
    @test trunc(-1//0) === trunc(Rational, -1//0) === -1//0
    @test floor(-1//0) === floor(Rational, -1//0) === -1//0
    @test ceil(-1//0) === ceil(Rational, -1//0) === -1//0
    for r = [RoundNearest, RoundNearestTiesAway, RoundNearestTiesUp,
             RoundToZero, RoundUp, RoundDown]
        @test round(1//0, r) === 1//0
        @test round(-1//0, r) === -1//0
    end

    @test @inferred(round(1//0, digits=1)) === Inf
    @test @inferred(trunc(1//0, digits=2)) === Inf
    @test @inferred(floor(-1//0, sigdigits=1)) === -Inf
    @test @inferred(ceil(-1//0, sigdigits=2)) === -Inf
end

@testset "issue 1552" begin
    @test isa(rationalize(Int8, float(pi)), Rational{Int8})
    @test rationalize(Int8, float(pi)) == 22//7
    @test rationalize(Int64, 0.957762604052997) == 42499549//44373782
    @test rationalize(Int16, 0.929261477046077) == 11639//12525
    @test rationalize(Int16, 0.2264705884044309) == 77//340
    @test rationalize(Int16, 0.39999899264235683) == 2//5
    @test rationalize(Int16, 1.1264233500618559e-5) == 0//1
    @test rationalize(UInt16, 0.6666652791223875) == 2//3
    @test rationalize(Int8, 0.9374813124660655) == 15//16
    @test rationalize(Int8, 0.003803032342443835) == 0//1
end
# issue 3412
@test convert(Rational{Int32},0.5) === Int32(1)//Int32(2)

@testset "issue 16513" begin
    @test convert(Rational{Int32}, pi) == float(1068966896 // 340262731)
    @test convert(Rational{Int64}, pi) == float(1068966896 // 340262731)
end
@testset "issue 5935" begin
    @test rationalize(Int8,  nextfloat(0.1)) == 1//10
    @test rationalize(Int64, nextfloat(0.1)) == 300239975158034//3002399751580339
    @test rationalize(Int128,nextfloat(0.1)) == 300239975158034//3002399751580339
    @test rationalize(Int8,  nextfloat(0.1),tol=0.5eps(0.1)) == 1//10
    @test rationalize(Int64, nextfloat(0.1),tol=0.5eps(0.1)) == 379250494936463//3792504949364629
    @test rationalize(Int128,nextfloat(0.1),tol=0.5eps(0.1)) == 379250494936463//3792504949364629
    @test rationalize(Int8,  nextfloat(0.1),tol=1.5eps(0.1)) == 1//10
    @test rationalize(Int64, nextfloat(0.1),tol=1.5eps(0.1)) == 1//10
    @test rationalize(Int128,nextfloat(0.1),tol=1.5eps(0.1)) == 1//10
    @test rationalize(Int64, nextfloat(0.1),tol=0) == 7205759403792795//72057594037927936
    @test rationalize(Int128,nextfloat(0.1),tol=0) == 7205759403792795//72057594037927936

    @test rationalize(Int8,  prevfloat(0.1)) == 1//10
    @test rationalize(Int64, prevfloat(0.1)) == 1//10
    @test rationalize(Int128,prevfloat(0.1)) == 1//10
    @test rationalize(Int64, prevfloat(0.1),tol=0) == 7205759403792793//72057594037927936
    @test rationalize(Int128,prevfloat(0.1),tol=0) == 7205759403792793//72057594037927936

    @test rationalize(Int8, 200f0) == 1//0
    @test rationalize(Int8, -200f0) == -1//0

    @test [rationalize(1pi,tol=0.1^n) for n=1:10] == [
                 16//5
                 22//7
                201//64
                333//106
                355//113
                355//113
              75948//24175
             100798//32085
             103993//33102
             312689//99532 ]
end

@testset "issue #12536" begin
    @test Rational{Int16}(1,2) === Rational(Int16(1),Int16(2))
    @test Rational{Int16}(500000,1000000) === Rational(Int16(1),Int16(2))
end
# issue 16311
rationalize(nextfloat(0.0)) == 0//1

@testset "rational-exponent promotion rules (issue #3155)" begin
    @test 2.0f0^(1//3) == 2.0f0^(1.0f0/3)
    @test 2^(1//3) == 2^(1/3)
end

@testset "overflow in rational comparison" begin
    @test 3//2 < typemax(Int)
    @test 3//2 <= typemax(Int)
end

# issue #15920
@test Rational(0, 1) / Complex(3, 2) == 0

# issue #16282
@test_throws MethodError 3 // 4.5im

# issue #31396
@test round(1//2, RoundNearestTiesUp) === 1//1

@testset "Unary plus on Rational (issue #30749)" begin
   @test +Rational(true) == 1//1
   @test +Rational(false) == 0//1
   @test -Rational(true) == -1//1
   @test -Rational(false) == 0//1
end

# issue #27039
@testset "gcd, lcm, gcdx for Rational" begin
    for T in (Int8, UInt8, Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, UInt128)
        a = T(6) // T(35)
        b = T(10) // T(21)
        @test gcd(a, b) === T(2)//T(105)
        @test gcd(b, a) === T(2)//T(105)
        @test lcm(a, b) === T(30)//T(7)
        if T <: Signed
            @test gcd(-a) === a
            @test lcm(-b) === b
            @test gcdx(a, b) === (T(2)//T(105), T(-11), T(4))
            @test gcd(-a, b) === T(2)//T(105)
            @test gcd(a, -b) === T(2)//T(105)
            @test gcd(-a, -b) === T(2)//T(105)
            @test lcm(-a, b) === T(30)//T(7)
            @test lcm(a, -b) === T(30)//T(7)
            @test lcm(-a, -b) === T(30)//T(7)
            @test gcdx(-a, b) === (T(2)//T(105), T(11), T(4))
            @test gcdx(a, -b) === (T(2)//T(105), T(-11), T(-4))
            @test gcdx(-a, -b) === (T(2)//T(105), T(11), T(-4))
        end

        @test gcd(a, T(0)//T(1)) === a
        @test lcm(a, T(0)//T(1)) === T(0)//T(1)
        @test gcdx(a, T(0)//T(1)) === (a, T(1), T(0))

        @test gcdx(T(1)//T(0), T(1)//T(2)) === (T(1)//T(0), T(1), T(0))
        @test gcdx(T(1)//T(2), T(1)//T(0)) === (T(1)//T(0), T(0), T(1))
        @test gcdx(T(1)//T(0), T(1)//T(1)) === (T(1)//T(0), T(1), T(0))
        @test gcdx(T(1)//T(1), T(1)//T(0)) === (T(1)//T(0), T(0), T(1))
        @test gcdx(T(1)//T(0), T(1)//T(0)) === (T(1)//T(0), T(1), T(1))
        @test gcdx(T(1)//T(0), T(0)//T(1)) === (T(1)//T(0), T(1), T(0))
        @test gcdx(T(0)//T(1), T(0)//T(1)) === (T(0)//T(1), T(1), T(0))

        if T <: Signed
            @test gcdx(T(-1)//T(0), T(1)//T(2)) === (T(1)//T(0), T(1), T(0))
            @test gcdx(T(1)//T(2), T(-1)//T(0)) === (T(1)//T(0), T(0), T(1))
            @test gcdx(T(-1)//T(0), T(1)//T(1)) === (T(1)//T(0), T(1), T(0))
            @test gcdx(T(1)//T(1), T(-1)//T(0)) === (T(1)//T(0), T(0), T(1))
            @test gcdx(T(-1)//T(0), T(1)//T(0)) === (T(1)//T(0), T(1), T(1))
            @test gcdx(T(1)//T(0), T(-1)//T(0)) === (T(1)//T(0), T(1), T(1))
            @test gcdx(T(-1)//T(0), T(-1)//T(0)) === (T(1)//T(0), T(1), T(1))
            @test gcdx(T(-1)//T(0), T(0)//T(1)) === (T(1)//T(0), T(1), T(0))
            @test gcdx(T(0)//T(1), T(-1)//T(0)) === (T(1)//T(0), T(0), T(1))
        end

        @test gcdx(T(1)//T(3), T(2)) === (T(1)//T(3), T(1), T(0))
        @test lcm(T(1)//T(3), T(1)) === T(1)//T(1)
        @test lcm(T(3)//T(1), T(1)//T(0)) === T(3)//T(1)
        @test lcm(T(0)//T(1), T(1)//T(0)) === T(0)//T(1)

        @test lcm(T(1)//T(0), T(1)//T(2)) === T(1)//T(2)
        @test lcm(T(1)//T(2), T(1)//T(0)) === T(1)//T(2)
        @test lcm(T(1)//T(0), T(1)//T(1)) === T(1)//T(1)
        @test lcm(T(1)//T(1), T(1)//T(0)) === T(1)//T(1)
        @test lcm(T(1)//T(0), T(1)//T(0)) === T(1)//T(0)
        @test lcm(T(1)//T(0), T(0)//T(1)) === T(0)//T(1)
        @test lcm(T(0)//T(1), T(0)//T(1)) === T(0)//T(1)

        if T <: Signed
            @test lcm(T(-1)//T(0), T(1)//T(2)) === T(1)//T(2)
            @test lcm(T(1)//T(2), T(-1)//T(0)) === T(1)//T(2)
            @test lcm(T(-1)//T(0), T(1)//T(1)) === T(1)//T(1)
            @test lcm(T(1)//T(1), T(-1)//T(0)) === T(1)//T(1)
            @test lcm(T(-1)//T(0), T(1)//T(0)) === T(1)//T(0)
            @test lcm(T(1)//T(0), T(-1)//T(0)) === T(1)//T(0)
            @test lcm(T(-1)//T(0), T(-1)//T(0)) === T(1)//T(0)
            @test lcm(T(-1)//T(0), T(0)//T(1)) === T(0)//T(1)
            @test lcm(T(0)//T(1), T(-1)//T(0)) === T(0)//T(1)
        end

        @test gcd([T(5), T(2), T(1)//T(2)]) === T(1)//T(2)
        @test gcd(T(5), T(2), T(1)//T(2)) === T(1)//T(2)

        @test lcm([T(5), T(2), T(1)//T(2)]) === T(10)//T(1)
        @test lcm(T(5), T(2), T(1)//T(2)) === T(10)//T(1)
    end
end

@testset "Binary operations with Integer" begin
    @test 1//2 - 1 == -1//2
    @test -1//2 + 1 == 1//2
    @test 1 - 1//2 == 1//2
    @test 1 + 1//2 == 3//2
    for q in (19//3, -4//5), i in (6, -7)
        @test rem(q, i) == q - i*div(q, i)
        @test mod(q, i) == q - i*fld(q, i)
    end
    @test 1//2 * 3 == 3//2
    @test -3 * (1//2) == -3//2
    @test (6//5) // -3 == -2//5
    @test -4 // (-6//5) == 10//3

    @test_throws OverflowError UInt(1)//2 - 1
    @test_throws OverflowError 1 - UInt(5)//2
    @test_throws OverflowError 1//typemax(Int64) + 1
    @test_throws OverflowError Int8(1) + Int8(5)//(Int8(127)-Int8(1))
    @test_throws InexactError UInt(1)//2 * -1
    @test_throws OverflowError typemax(Int64)//1 * 2
    @test_throws OverflowError -1//1 * typemin(Int64)

    @test Int8(1) + Int8(4)//(Int8(127)-Int8(1)) == Int8(65) // Int8(63)
    @test -Int32(1) // typemax(Int32) - Int32(1) == typemin(Int32) // typemax(Int32)
end

@testset "Promotions on binary operations with Rationals (#36277)" begin
    inttypes = (Base.BitInteger_types..., )
    for T in inttypes, S in inttypes
        U = Rational{promote_type(T, S)}
        @test typeof(one(Rational{T}) + one(S)) == typeof(one(S) + one(Rational{T})) == typeof(one(Rational{T}) + one(Rational{S})) == U
        @test typeof(one(Rational{T}) - one(S)) == typeof(one(S) - one(Rational{T})) == typeof(one(Rational{T}) - one(Rational{S})) == U
        @test typeof(one(Rational{T}) * one(S)) == typeof(one(S) * one(Rational{T})) == typeof(one(Rational{T}) * one(Rational{S})) == U
        @test typeof(one(Rational{T}) // one(S)) == typeof(one(S) // one(Rational{T})) == typeof(one(Rational{T}) // one(Rational{S})) == U
    end
    @test (-40//3) // 0x5 == 0x5 // (-15//8) == -8//3
    @test (-4//7) // (0x1//0x3) == (0x4//0x7) // (-1//3) == -12//7
    @test -3//2 + 0x1//0x1 == -3//2 + 0x1 == 0x1//0x1 + (-3//2) == 0x1 + (-3//2) == -1//2
    @test 0x3//0x5 - 2//3 == 3//5 - 0x2//0x3 == -1//15
    @test rem(-12//5, 0x2//0x1) == rem(-12//5, 0x2) == -2//5
    @test mod(0x3//0x1, -4//7) == mod(0x3, -4//7) == -3//7
    @test -1//5 * 0x3//0x2 == 0x3//0x2 * -1//5 == -3//10
    @test -2//3 * 0x1 == 0x1 * -2//3 == -2//3
end

@testset "ispow2 and iseven/isodd" begin
    @test ispow2(4//1)
    @test ispow2(1//8)
    @test !ispow2(3//8)
    @test !ispow2(0//1)
    @test iseven(4//1) && !isodd(4//1)
    @test !iseven(3//1) && isodd(3//1)
    @test !iseven(3//8) && !isodd(3//8)
end

@testset "checked_den with different integer types" begin
    @test Base.checked_den(Int8(4), Int32(8)) == Base.checked_den(Int32(4), Int32(8))
end

@testset "Rational{T} with non-concrete T (issue #41222)" begin
    @test @inferred(Rational{Integer}(2,3)) isa Rational{Integer}
end

@testset "issue #41489" begin
    @test Core.Compiler.return_type(+, NTuple{2, Rational}) == Rational
    @test Core.Compiler.return_type(-, NTuple{2, Rational}) == Rational

    A=Rational[1 1 1; 2 2 2; 3 3 3]
    @test @inferred(A*A) isa Matrix{Rational}
end

@testset "issue #42560" begin
    @test rationalize(0.5 + 0.5im) == 1//2 + 1//2*im
    @test rationalize(float(pi)im) == 0//1 + 165707065//52746197*im
    @test rationalize(Int8, float(pi)im) == 0//1 + 22//7*im
    @test rationalize(1.192 + 2.233im) == 149//125 + 2233//1000*im
    @test rationalize(Int8, 1.192 + 2.233im) == 118//99 + 67//30*im
end
