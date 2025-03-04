# This file is a part of Julia. License is MIT: https://julialang.org/license

using Test, Random

# test the basic floating point functions

@testset "flipsign" begin
    for elty in (Float32,Float64)
        x = convert(elty,-2.0)
        x = flipsign(x,-1.0)
        @test flipsign(x,float(-1.0)) == convert(elty,-2.0)
    end
end

@testset "maxintfloat" begin
    @test maxintfloat(Float16) === Float16(2048f0)
    for elty in (Float16,Float32,Float64)
        @test maxintfloat(rand(elty)) === maxintfloat(elty)
    end
    @test maxintfloat() === maxintfloat(Float64)
    @test maxintfloat(Float64, Int32) === 2147483647.0
    @test maxintfloat(Float32, Int32) === maxintfloat(Float32)
    @test maxintfloat(Float64, Int16) === 32767.0
    @test maxintfloat(Float64, Int64) === maxintfloat(Float64)
end

@testset "isinteger" begin
    for elty in (Float16, Float32, Float64)
        @test !isinteger(elty(1.2))
        @test isinteger(elty(12))
        @test isinteger(zero(elty))
        @test isinteger(-zero(elty))
        @test !isinteger(nextfloat(zero(elty)))
        @test !isinteger(prevfloat(zero(elty)))
        @test isinteger(maxintfloat(elty))
        @test isinteger(-maxintfloat(elty))
        @test !isinteger(elty(Inf))
        @test !isinteger(-elty(Inf))
        @test !isinteger(elty(NaN))
    end
end

@testset "ispow2 and iseven/isodd" begin
    for T in (Float16,Float32,Float64)
        for x in (0.25, 1.0, 4.0, exp2(T(exponent(floatmax(T)))), exp2(T(exponent(floatmin(T)))))
            @test ispow2(T(x))
        end
        for x in (1.5, 0.0, 7.0, NaN, Inf)
            @test !ispow2(T(x))
        end
        for x in (0, 134)
            @test iseven(T(x)) && iseven(T(-x))
            @test isodd(T(x+1)) && isodd(T(-x-1))
        end
        let x = maxintfloat(T) * π
            @test iseven(x) && iseven(-x)
            @test !isodd(x) && !isodd(-x)
        end
        @test !iseven(0.5) && !isodd(0.5)
    end
end

@testset "round" begin
    for elty in (Float32, Float64)
        x = rand(elty)
        A = fill(x,(10,10))
        @test round.(A,RoundToZero) == fill(trunc(x),(10,10))
        @test round.(A,RoundUp) == fill(ceil(x),(10,10))
        @test round.(A,RoundDown) == fill(floor(x),(10,10))
        A = fill(x,(10,10,10))
        @test round.(A,RoundToZero) == fill(trunc(x),(10,10,10))
        @test round.(A,RoundUp) == fill(ceil(x),(10,10,10))
        @test round.(A,RoundDown) == fill(floor(x),(10,10,10))
        for elty2 in (Int32,Int64)
            A = fill(x,(10,))
            @test round.(elty2,A,RoundToZero) == fill(trunc(elty2,x),(10,))
            @test round.(elty2,A,RoundUp) == fill(ceil(elty2,x),(10,))
            @test round.(elty2,A,RoundDown) == fill(floor(elty2,x),(10,))
            A = fill(x,(10,10))
            @test round.(elty2,A,RoundToZero) == fill(trunc(elty2,x),(10,10))
            @test round.(elty2,A,RoundUp) == fill(ceil(elty2,x),(10,10))
            @test round.(elty2,A,RoundDown) == fill(floor(elty2,x),(10,10))
            A = fill(x,(10,10,10))
            @test round.(elty2,A,RoundToZero) == fill(trunc(elty2,x),(10,10,10))
            @test round.(elty2,A,RoundUp) == fill(ceil(elty2,x),(10,10,10))
            @test round.(elty2,A,RoundDown) == fill(floor(elty2,x),(10,10,10))
            @test round.(elty2,A) == fill(round(elty2,x),(10,10,10))
        end
    end
end

@testset "Types" begin
    for x in (Int16(0), 1, 2f0, pi, 3//4, float(5//6), 7.8, float(9), float(ℯ))
        @test float(typeof(x)) == typeof(float(x))
        @test float(typeof(complex(x, x))) == typeof(float(complex(x, x)))
    end
end

@testset "significant digits" begin
    # (would be nice to have a smart vectorized
    # version of signif)
    @test round(123.456, sigdigits=1) ≈ 100.
    @test round(123.456, sigdigits=3) ≈ 123.
    @test round(123.456, sigdigits=5) ≈ 123.46
    @test round(123.456, sigdigits=8, base = 2) ≈ 123.5
    @test round(123.456, sigdigits=2, base = 4) ≈ 128.0
    @test round(0.0, sigdigits=1) === 0.0
    @test round(-0.0, sigdigits=1) === -0.0
    @test round(1.2, sigdigits=2) === 1.2
    @test round(1.0, sigdigits=6) === 1.0
    @test round(0.6, sigdigits=1) === 0.6
    @test round(7.262839104539736, sigdigits=2) === 7.3
    @test isinf(round(Inf, sigdigits=3))
    @test isnan(round(NaN, sigdigits=3))
    @test round(1.12312, sigdigits=1000) === 1.12312
    @test round(Float32(7.262839104539736), sigdigits=3) === Float32(7.26)
    @test round(Float32(7.262839104539736), sigdigits=4) === Float32(7.263)
    @test round(Float32(1.2), sigdigits=3) === Float32(1.2)
    @test round(Float32(1.2), sigdigits=5) === Float32(1.2)
    @test round(Float16(0.6), sigdigits=2) === Float16(0.6)
    @test round(Float16(1.1), sigdigits=70) === Float16(1.1)

    # issue 37171
    @test round(9.87654321e-308, sigdigits = 1) ≈ 1.0e-307
    @test round(9.87654321e-308, sigdigits = 2) ≈ 9.9e-308
    @test round(9.87654321e-308, sigdigits = 3) ≈ 9.88e-308
    @test round(9.87654321e-308, sigdigits = 4) ≈ 9.877e-308
    @test round(9.87654321e-308, sigdigits = 5) ≈ 9.8765e-308
    @test round(9.87654321e-308, sigdigits = 6) ≈ 9.87654e-308
    @test round(9.87654321e-308, sigdigits = 7) ≈ 9.876543e-308
    @test round(9.87654321e-308, sigdigits = 8) ≈ 9.8765432e-308
    @test round(9.87654321e-308, sigdigits = 9) ≈ 9.87654321e-308
    @test round(9.87654321e-308, sigdigits = 10) ≈ 9.87654321e-308
    @test round(9.87654321e-308, sigdigits = 11) ≈ 9.87654321e-308

    @inferred round(Float16(1.), sigdigits=2)
    @inferred round(Float32(1.), sigdigits=2)
    @inferred round(Float64(1.), sigdigits=2)
end

@testset "literal pow matches runtime pow matches optimized pow" begin
    two = 2
    @test 1.0000000105367122^2 == 1.0000000105367122^two
    @test 1.0041504f0^2 == 1.0041504f0^two

    function g2(start, two, N)
        x = start
        n = 0
        for _ in 1:N
           n += (x^2 !== x^two)
           x = nextfloat(x)
        end
        return n
    end
    @test g2(1.0, 2, 100_000_000) == 0
    @test g2(1.0f0, 2, 100_000_000) == 0
    g2′(start, N) = g2(start, 2, N)
    @test g2′(1.0, 100_000_000) == 0
    @test g2′(1.0f0, 100_000_000) == 0

    function g3(start, three, N)
        x = start
        n = 0
        for _ in 1:N
           n += (x^3 !== x^three)
           x = nextfloat(x)
        end
        return n
    end
    @test g3(1.0, 3, 100_000_000) == 0
    @test g3(1.0f0, 3, 100_000_000) == 0
    g3′(start, N) = g3(start, 3, N)
    @test g3′(1.0, 100_000_000) == 0
    @test g3′(1.0f0, 100_000_000) == 0

    function ginv(start, inv, N)
        x = start
        n = 0
        for _ in 1:N
           n += (x^-1 !== x^inv)
           x = nextfloat(x)
        end
        return n
    end
    @test ginv(1.0, -1, 100_000_000) == 0
    @test ginv(1.0f0, -1, 100_000_000) == 0
    ginv′(start, N) = ginv(start, -1, N)
    @test ginv′(1.0, 100_000_000) == 0
    @test ginv′(1.0f0, 100_000_000) == 0

    f(x, p) = x^p
    finv(x) = f(x, -1)
    f2(x) = f(x, 2)
    f3(x) = f(x, 3)
    x = 1.0000000105367122
    @test x^2 == f(x, 2) == f2(x) == x*x == Float64(float(x)*float(x))
    @test x^3 == f(x, 3) == f3(x) == x*x*x == Float64(float(x)*float(x)*float(x))
    x = 1.000000007393669
    @test x^-1 == f(x, -1) == finv(x) == 1/x == inv(x) == Float64(1/float(x)) == Float64(inv(float(x)))
end

@testset "curried approximation" begin

    @test ≈(1.0; atol=1).(1.0:3.0) == [true, true, false]

end

@testset "isnan for Number" begin
    struct CustomNumber <: Number end
    @test !isnan(CustomNumber())
end
