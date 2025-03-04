# This file is a part of Julia. License is MIT: https://julialang.org/license

"""
    Base.MathConstants

Module containing the mathematical constants.
See [`π`](@ref), [`ℯ`](@ref), [`γ`](@ref), [`φ`](@ref) and [`catalan`](@ref).
"""
module MathConstants

export π, pi, ℯ, e, γ, eulergamma, catalan, φ, golden

Base.@irrational π        3.14159265358979323846  pi
Base.@irrational ℯ        2.71828182845904523536  exp(Float64(1))
Base.@irrational γ        0.57721566490153286061  euler
Base.@irrational φ        1.61803398874989484820  (1+sqrt(Float64(5)))/2
Base.@irrational catalan  0.91596559417721901505  catalan

# aliases
"""
    π
    pi

The constant pi.

Unicode `π` can be typed by writing `\\pi` then pressing tab in the Julia REPL, and in many editors.

See also: [`sinpi`](@ref), [`sincospi`](@ref), [`deg2rad`](@ref).

# Examples
```jldoctest
julia> pi
π = 3.1415926535897...

julia> 1/2pi
0.15915494309189535
```
"""
π, const pi = π

"""
    ℯ
    e

The constant ℯ.

Unicode `ℯ` can be typed by writing `\\euler` and pressing tab in the Julia REPL, and in many editors.

See also: [`exp`](@ref), [`cis`](@ref), [`cispi`](@ref).

# Examples
```jldoctest
julia> ℯ
ℯ = 2.7182818284590...

julia> log(ℯ)
1

julia> ℯ^(im)π ≈ -1
true
```
"""
ℯ, const e = ℯ

"""
    γ
    eulergamma

Euler's constant.

# Examples
```jldoctest
julia> Base.MathConstants.eulergamma
γ = 0.5772156649015...

julia> dx = 10^-6;

julia> sum(-exp(-x) * log(x) for x in dx:dx:100) * dx
0.5772078382499133
```
"""
γ, const eulergamma = γ

"""
    φ
    golden

The golden ratio.

# Examples
```jldoctest
julia> Base.MathConstants.golden
φ = 1.6180339887498...

julia> (2ans - 1)^2 ≈ 5
true
```
"""
φ, const golden = φ

"""
    catalan

Catalan's constant.

# Examples
```jldoctest
julia> Base.MathConstants.catalan
catalan = 0.9159655941772...

julia> sum(log(x)/(1+x^2) for x in 1:0.01:10^6) * 0.01
0.9159466120554123
```
"""
catalan

# loop over types to prevent ambiguities for ^(::Number, x)
for T in (AbstractIrrational, Rational, Integer, Number, Complex)
    Base.:^(::Irrational{:ℯ}, x::T) = exp(x)
end
Base.literal_pow(::typeof(^), ::Irrational{:ℯ}, ::Val{p}) where {p} = exp(p)

Base.log(::Irrational{:ℯ}) = 1 # use 1 to correctly promote expressions like log(x)/log(ℯ)
Base.log(::Irrational{:ℯ}, x::Number) = log(x)

Base.sin(::Irrational{:π}) = 0.0
Base.cos(::Irrational{:π}) = -1.0
Base.sincos(::Irrational{:π}) = (0.0, -1.0)
Base.tan(::Irrational{:π}) = 0.0
Base.cot(::Irrational{:π}) = -1/0

end # module
