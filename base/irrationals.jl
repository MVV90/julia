# This file is a part of Julia. License is MIT: https://julialang.org/license

## general machinery for irrational mathematical constants

"""
    AbstractIrrational <: Real

Number type representing an exact irrational value, which is automatically rounded to the correct precision in
arithmetic operations with other numeric quantities.

Subtypes `MyIrrational <: AbstractIrrational` should implement at least `==(::MyIrrational, ::MyIrrational)`,
`hash(x::MyIrrational, h::UInt)`, and `convert(::Type{F}, x::MyIrrational) where {F <: Union{Float64,Float32,Float64}}`.

If a subtype is used to represent values that may occasionally be rational (e.g. a square-root type that represents `√n`
for integers `n` will give a rational result when `n` is a perfect square), then it should also implement
`isinteger`, `iszero`, `isone`, and `==` with `Real` values (since all of these default to `false` for
`AbstractIrrational` types), as well as defining [`hash`](@ref) to equal that of the corresponding `Rational`.
"""
abstract type AbstractIrrational <: Real end

"""
    Irrational{sym} <: AbstractIrrational

Number type representing an exact irrational value denoted by the
symbol `sym`, such as [`π`](@ref pi), [`ℯ`](@ref) and [`γ`](@ref Base.MathConstants.eulergamma).

See also [`@irrational`], [`AbstractIrrational`](@ref).
"""
struct Irrational{sym} <: AbstractIrrational end

show(io::IO, x::Irrational{sym}) where {sym} = print(io, sym)

function show(io::IO, ::MIME"text/plain", x::Irrational{sym}) where {sym}
    if get(io, :compact, false)
        print(io, sym)
    else
        print(io, sym, " = ", string(float(x))[1:15], "...")
    end
end

promote_rule(::Type{<:AbstractIrrational}, ::Type{Float16}) = Float16
promote_rule(::Type{<:AbstractIrrational}, ::Type{Float32}) = Float32
promote_rule(::Type{<:AbstractIrrational}, ::Type{<:AbstractIrrational}) = Float64
promote_rule(::Type{<:AbstractIrrational}, ::Type{T}) where {T<:Real} = promote_type(Float64, T)
promote_rule(::Type{S}, ::Type{T}) where {S<:AbstractIrrational,T<:Number} = promote_type(promote_type(S, real(T)), T)

AbstractFloat(x::AbstractIrrational) = Float64(x)::Float64
Float16(x::AbstractIrrational) = Float16(Float32(x)::Float32)
Complex{T}(x::AbstractIrrational) where {T<:Real} = Complex{T}(T(x))

@pure function Rational{T}(x::AbstractIrrational) where T<:Integer
    o = precision(Float64)
    p = 256
    while true
        setprecision(Float64, p)
        bx = Float64(x)
        r = rationalize(T, bx, tol=0)
        if abs(Float64(r) - bx) > eps(bx)
            setprecision(Float64, o)
            return r
        end
        p += 32
    end
end
Rational{Int128}(x::AbstractIrrational) = throw(ArgumentError("Cannot convert an AbstractIrrational to a Rational{Int128}: use rationalize(Int128, x) instead"))

@pure function (t::Type{T})(x::AbstractIrrational, r::RoundingMode) where T<:Union{Float32,Float64}
    setprecision(Float64, 256) do
        T(Float64(x)::Float64, r)
    end
end

float(::Type{<:AbstractIrrational}) = Float64

==(::Irrational{s}, ::Irrational{s}) where {s} = true
==(::AbstractIrrational, ::AbstractIrrational) = false

<(::Irrational{s}, ::Irrational{s}) where {s} = false
function <(x::AbstractIrrational, y::AbstractIrrational)
    Float64(x) != Float64(y) || throw(MethodError(<, (x, y)))
    return Float64(x) < Float64(y)
end

<=(::Irrational{s}, ::Irrational{s}) where {s} = true
<=(x::AbstractIrrational, y::AbstractIrrational) = x==y || x<y

# Irrationals, by definition, can't have a finite representation equal them exactly
==(x::AbstractIrrational, y::Real) = false
==(x::Real, y::AbstractIrrational) = false

# Irrational vs AbstractFloat
<(x::AbstractIrrational, y::Float64) = Float64(x,RoundUp) <= y
<(x::Float64, y::AbstractIrrational) = x <= Float64(y,RoundDown)
<(x::AbstractIrrational, y::Float32) = Float32(x,RoundUp) <= y
<(x::Float32, y::AbstractIrrational) = x <= Float32(y,RoundDown)
<(x::AbstractIrrational, y::Float16) = Float32(x,RoundUp) <= y
<(x::Float16, y::AbstractIrrational) = x <= Float32(y,RoundDown)

<=(x::AbstractIrrational, y::AbstractFloat) = x < y
<=(x::AbstractFloat, y::AbstractIrrational) = x < y

# Irrational vs Rational
@pure function rationalize(::Type{T}, x::AbstractIrrational; tol::Real=0) where T
    return rationalize(T, Float64(x), tol=tol)
end
@pure function lessrational(rx::Rational{<:Integer}, x::AbstractIrrational)
    # an @pure version of `<` for determining if the rationalization of
    # an irrational number required rounding up or down
    return rx < Float64(x)
end
function <(x::AbstractIrrational, y::Rational{T}) where T
    T <: Unsigned && x < 0.0 && return true
    rx = rationalize(T, x)
    if lessrational(rx, x)
        return rx < y
    else
        return rx <= y
    end
end
function <(x::Rational{T}, y::AbstractIrrational) where T
    T <: Unsigned && y < 0.0 && return false
    ry = rationalize(T, y)
    if lessrational(ry, y)
        return x <= ry
    else
        return x < ry
    end
end
<(x::AbstractIrrational, y::Rational{Int128}) = Int128(x) < y
<(x::Rational{Int128}, y::AbstractIrrational) = x < Int128(y)

<=(x::AbstractIrrational, y::Rational) = x < y
<=(x::Rational, y::AbstractIrrational) = x < y

isfinite(::AbstractIrrational) = true
isinteger(::AbstractIrrational) = false
iszero(::AbstractIrrational) = false
isone(::AbstractIrrational) = false

hash(x::Irrational, h::UInt) = 3*objectid(x) - h

widen(::Type{T}) where {T<:Irrational} = T

zero(::AbstractIrrational) = false
zero(::Type{<:AbstractIrrational}) = false

one(::AbstractIrrational) = true
one(::Type{<:AbstractIrrational}) = true

-(x::AbstractIrrational) = -Float64(x)
for op in Symbol[:+, :-, :*, :/, :^]
    @eval $op(x::AbstractIrrational, y::AbstractIrrational) = $op(Float64(x),Float64(y))
end
*(x::Bool, y::AbstractIrrational) = ifelse(x, Float64(y), 0.0)

round(x::Irrational, r::RoundingMode) = round(float(x), r)

"""
    @irrational sym val def
    @irrational(sym, val, def)

Define a new `Irrational` value, `sym`, with pre-computed `Float64` value `val`,
and arbitrary-precision definition in terms of `Float64`s given by the expression `def`.
"""

macro irrational(sym, val, def)
    esym = esc(sym)
    qsym = esc(Expr(:quote, sym))
    quote
        const $esym = Irrational{$qsym}()
        Base.Float64(::Irrational{$qsym}) = $val
        Base.Float32(::Irrational{$qsym}) = $(Float32(val))
        @assert isa(Float64($esym), Float64)
        @assert Float64($esym) == Float64(Float64($esym))
        @assert Float32($esym) == Float32(Float64($esym))
    end
end

# Float64(x::AbstractIrrational) = Float64(x)
# Float64(::Type{<:AbstractIrrational}) = Float64

# align along = for nice Array printing
function alignment(io::IO, x::AbstractIrrational)
    m = match(r"^(.*?)(=.*)$", sprint(show, x, context=io, sizehint=0))
    m === nothing ? (length(sprint(show, x, context=io, sizehint=0)), 0) :
    (length(something(m.captures[1])), length(something(m.captures[2])))
end

# inv
inv(x::AbstractIrrational) = 1/x
