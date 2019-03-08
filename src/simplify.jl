## hack attempts to provide some of SymPy's simplify routines.
## could be seriously improved


## + expand  (built in)
##
## + expand_log
## + expand_power_exp
## + expand_power_base
## + expand_trig


## + logcombine (logsimp)
## + powsimp
## + powdenest
## * combsimp
## + trigsimp


## * factor (over Q)
## * collect
## * coeffs
## * cancel
## * apart

### --------------------------------------------------

export trig_simp, expand_trig


get_fun(ex::BasicType{Val{:Add}}) = :(+)
get_fun(ex::BasicType{Val{:Sub}}) = :(-)
get_fun(ex::BasicType{Val{:Mul}}) = :(*)
get_fun(ex::BasicType{Val{:Div}}) = :(/)
get_fun(ex::BasicType{Val{:Pow}}) = :(^)
#for t in (:Symbol, :Integer, :Rational, :Complex) ...
get_fun(ex::BasicType{Val{:Symbol}}) = :identity
get_fun(ex::BasicType{Val{:Integer}}) = :identity
get_fun(ex::BasicType{Val{:Rational}}) = :identity
get_fun(ex::BasicType{Val{:Complex}}) = :identity

function get_fun(u::BasicType)
    ex = Basic(u)
    as = args(ex)
    fn = head(ex) |> string |> lowercase |> Symbol
    fn
end

abstract type AbstractSimplify end

## identities



## rewrite product of sin and cos

## sin(x)*cos(y) = 1/2 * (sin(x+y) + sin(x-y)) ...
function sc(ex)
    @vars u_ v_ x___
    out = replace(ex,
                  sin(u_)*cos(v_)*x___,
                  (isempty(x___) ? Basic(1) : prod(x___)) * (sin(expand(v_ + u_)) + sin(expand(u_ - v_))))
    expand(out)
end

function ss(ex)
    @vars u_ v_ x___
    out = replace(ex,
                  sin(u_)*sin(v_)*x___,
                  x___*(1//2)*(cos(expand(u_ - v_)) - cos(expand(u_ + v_))))
    expand(out)
end

function cc(ex)
    @vars u_ v_ x___
    out = replace(ex,
                  cos(u_)*cos(v_)*x___,
                  x___ * (1//2)*(cos(expand(u_ + v_)) + cos(expand(u_ - v_))))
    expand(out)
end

## hyperbolic
function shch(ex)
    @vars u_ v_ x___
    out = replace(ex,
                  sinh(u_)*cosh(v_)*x___,
                  x___*(1//2)*(sinh(expand(v_ + u_)) + sinh(expand(u_ - v_))))
    expand(out)
end

function shsh(ex)
    @vars u_ v_ x___
    out = replace(ex,
                  sinh(u_)*sinh(v_)*x___,
                  x___*(1//2)*(cosh(expand(u_ + v_))- cosh(expand(u_ - v_)) ))
    expand(out)
end

function chch(ex)
    @vars u_ v_ x___
    out = replace(ex,
                  cosh(u_)*cosh(v_)*x___,
                  x___ * (1//2)*(cosh(expand(u_ + v_)) + cosh(expand(u_ - v_))))
    expand(out)
end


### expand trig -- sin(x+y) -> sin(x)*sin(y) + cos(x)*cos(y)
function sxy(ex)
    @vars x_ y_ x___
    ex = replace(ex, sin(x_ + y_) * x___ => x___ * (sin(x_)*cos(y_) + sin(y_) * cos(x_)))
#    m = match(ex, sin(x_*y_))
#    !ismatch(m) && return ex
    #    is XX Number(x_) or Number(y_) and integer and agreater 2 then write as 2x + (n-2)x and expand#...
    ex
end

function cxy(ex)
    @vars x_ y_ x___
    replace(ex, cos(x_ + y_) * x___ => x___ * (cos(x_)*cos(y_) - sin(x_) * sin(y_)))
end

##################################################

##
## The basic _simp functions walk the syntax tree
## the specialized types then define what happens
## when the walking occurs with overrides as needed
function _simp(T::AbstractSimplify, ex::BasicType{Val{:Add}})
    sum(_simp(T, a) for a in args(Basic(ex)))
end

function _simp(T::AbstractSimplify, ex::BasicType{Val{:Mul}})
    prod(_simp(T, a) for a in args(Basic(ex)))
end

## "canonicalize" trig, hyperbolic, to use sin,cos or sinh, cosh
## Could make this a separate simplification, but that would
## involve walking the syntax tree again
_simp(::AbstractSimplify, ex::BasicType{Val{:Tan}}) = (u = args(Basic(ex));sin(u...)/cos(u...))
_simp(::AbstractSimplify, ex::BasicType{Val{:Cot}}) = (u = args(Basic(ex));cos(u...)/sin(u...))
_simp(::AbstractSimplify, ex::BasicType{Val{:Sec}}) = (u = args(Basic(ex));inv(cos(u...)))
_simp(::AbstractSimplify, ex::BasicType{Val{:Csc}}) = (u = args(Basic(ex));inv(sin(u...)))

_simp(::AbstractSimplify, ex::BasicType{Val{:Tanh}}) = (u = args(Basic(ex));sinh(u...)/cosh(u...))
_simp(::AbstractSimplify, ex::BasicType{Val{:Coth}}) = (u = args(Basic(ex));cosh(u...)/sinh(u...))
_simp(::AbstractSimplify, ex::BasicType{Val{:Sech}}) = (u = args(Basic(ex));inv(cosh(u...)))
_simp(::AbstractSimplify, ex::BasicType{Val{:Csch}}) = (u = args(Basic(ex));inv(sinh(u...)))

## leaves -- when args(ex) = []
function _simp(::AbstractSimplify, ex::T) where {T <: SymEngine.BasicNumber}
    Basic(ex)
end

function _simp(::AbstractSimplify, ex::BasicType{Val{:Symbol}})
    Basic(ex)
end

## catch all
function _simp(T::AbstractSimplify, ex::BasicType)
#    println("_simp: $ex $(typeof(ex))")
    eval(Expr(:call, get_fun(ex), broadcast(_simp, T, args(Basic(ex)))...))
end
_simp(T::AbstractSimplify, ex::Basic) = _simp(T, BasicType(ex))


## iterate until a fixed point
function _fixed_point(T::AbstractSimplify, ex, n=20)
    for i in 1:n
        ex1 = _simp(T, BasicType(ex))
        ex1 == ex && return expand(ex)
        ex = ex1
    end
    expand(ex)
end



##################################################

## check that walking works
struct BlankSimp <: AbstractSimplify end

##################################################
## TrigSimp
struct TrigSimp <: AbstractSimplify end

"""
    trig_simp

Expand trig products such as `sin(x)*cos(y)` into sums using double angle
formulas
"""
trig_simp(ex::Basic) = _fixed_point(TrigSimp(), ex)

function _simp(T::TrigSimp, ex::BasicType{Val{:Pow}})
    a,b = args(Basic(ex))
    if  head(b) == :Integer && b > 1
        @vars u_
        op = head(a)
        op == :Sin  && return replace(a^2, sin(u_)^2,   1//2*(1 - cos(2*u_)))  * a^(b-2)
        op == :Cos  && return replace(a^2, cos(u_)^2,   1//2*(1 + cos(2*u_)))  * a^(b-2)
        op == :Sinh && return replace(a^2, sinh(u_)^2, -1//2*(1 - cosh(2*u_))) * a^(b-2)
        op == :Cosh && return replace(a^2, cosh(u_)^2,  1//2*(1 + cosh(2*u_))) * a^(b-2)
    elseif head(b) == :Integer && b <= -1
        return _simp(T, a)^b
    end
    return ex
end


## products apply the simplification rules for sin*cos,...
function _simp(T::TrigSimp, ex::BasicType{Val{:Mul}})
    v = Basic(ex)
    u = v |> cc |> ss |> sc |> chch |> shsh |> shch
    u = expand(u)
    head(u) != :Mul && return u
    out = Basic(1)

    ## out =prod(_simp(T, a) for a in args(Basic(u)))
    for a in args(Basic(u))
        out = out * _simp(T, a)
    end
    return out
end

##################################################
## expand trig
struct ExpandTrig <: AbstractSimplify end

"""
    expand_trig

Apply double angle formulas to express as products of sines and cosines
"""
expand_trig(ex::Basic) = _fixed_point(ExpandTrig(), ex)

_simp(T::ExpandTrig, ex::BasicType{Val{:Sin}}) = sxy(Basic(ex))
_simp(T::ExpandTrig, ex::BasicType{Val{:Cos}}) = cxy(Basic(ex))


##################################################
