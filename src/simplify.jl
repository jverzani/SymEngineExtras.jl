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
## * trigsimp


## * factor (over Q)
## * collect
## * coeffs
## * cancel
## * apart

## * rewrite

export simplify, logsimp, powsimp, powdenest, trigsimp
export expand_log, expand_power_exp, expand_power_base, expand_trig
export rewrite_trig


function simplify(ex::Basic)
    ex = logsimp(ex)
    ex = powsimp(ex)
    ex = powdenest(ex)
    ex = trigsimp(ex)
    ex
end


## logsimp
## a * log(b) -> log(b^a)
## log(a) + log(b) = log(a*b)
## was 5 times faster than SymPy logcombine
function logsimp(ex::Basic; recurse::Bool=true)
    ex1 = Basic(logsimp(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(logsimp(BasicType(ex)))
    end
    ex1
end

function logsimp(ex::BasicType{Val{:Mul}})
    
    m = pattern_match(ex, _1 * log(_2))
    if m.match
        return log(m.matches[_2]^m.matches[_1])
    end
    m = pattern_match(ex, log(_2) * _1)
    if m.match
        return log(m.matches[_2]^m.matches[_1])
    end
    prod(map(logsimp, get_args(ex)))
end
        

function logsimp(ex::BasicType{Val{:Add}})
    as = get_args(ex)
    n = length(as)
    ms = PatternMatch[pattern_match(a, log(_1)) for a in as]
    is = filter(i -> ms[i].match, 1:n)

    mats = Basic[ms[i].matches[_1] for i in is]
    nmats = Basic[logsimp(as[j]) for j in setdiff(1:n, is)]

    log(prod(mats)) + sum(nmats)
end

function logsimp(ex::BasicType{Val{:Log}})
    log(logsimp(get_args(ex)[1]))
end

function logsimp(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(logsimp, as)...))
    end
end


## expand_log
## a * log(b) -> log(b^a)
## log(a) + log(b) = log(a*b)
function expand_log(ex::Basic; recurse::Bool=true)
    ex1 = Basic(expand_log(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(expand_log(BasicType(ex)))
    end

    ex1
end

function expand_log(ex::BasicType{Val{:Log}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)

    ## we expand Mul, Div and Pow
    if ty == :Mul
        mas = get_args(arg)
        return sum([log(expand_log(m)) for m in mas])
    elseif ty == :Div
        mas = get_args(arg)
        return log(expand_log(mas[1])) - log(expand_log(mas[2]))
    elseif ty == :Pow
        mas = get_args(arg)
        return expand_log(mas[2]) * log(mas[1])
    else
        log(expand_log(arg))
    end
end
        


function expand_log(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(expand_log, as)...))
    end
end




## powsimp


## powsimp
## x^a * x^b = x^(a+b)  ## mostly done!
## x^a * y^a = (x*y)^a  ## but ... undone by SymEngine
function powsimp(ex::Basic; recurse::Bool=true)
    ex1 = Basic(powsimp(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(powsimp(BasicType(ex)))
    end
    ex1
end

function powsimp(ex::BasicType{Val{:Pow}})
    as = get_args(ex)
    if get_symengine_class(as[2]) == :Mul
        bs = get_args(as[2])
        (as[1]^bs[1])^powsimp(bs[2])
    else
        as[1]^powsimp(as[2])
    end
end

    
## 
function powsimp(ex::BasicType{Val{:Mul}})

    # x^n * y^n -> (x*y)^n
    out = pattern_match(ex, _1^_2 * _3^2 * ___)
    if out.match
        a,b,n,c = out.matches[_1], out.matches[_3], out.matches[_2], get(out.matches,___, Basic(1))
        ex = (a * b)^n * c
    end

    out = pattern_match(ex, _1^2 * _1^_3 * ___)
    if out.match
        a,n,m,c = out.matches[_1], out.matches[_2], out.matches[_3], get(out.matches,___, Basic(1))
        println((ex, a,b,c,n))
        ex = a^(n+m) * c
    end
    
    ex
end
        

function powsimp(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(powsimp, as)...))
    end
end
        

## powdenest
## a^(b*c) = (a^b)^c
function powdenest(ex::Basic; recurse::Bool=true)
    ex1 = Basic(powdenest(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(powdenest(BasicType(ex)))
    end
    ex1
end

function powdenest(ex::BasicType{Val{:Pow}})
    as = get_args(ex)
    if get_symengine_class(as[2]) == :Mul
        bs = get_args(as[2])
        (as[1]^bs[1])^powdenest(bs[2])
    else
        as[1]^powdenest(as[2])
    end
end

    
   

function powdenest(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(powdenest, as)...))
    end
end




## expand_power_exp / expand_power_base¶
## expand_power_exp = x^(a+b) = x^a x^b  ## fighting tide, as SymEngine simplifies
## expand_power_base = (x*y)^a = x^a * y^a

function expand_power_exp(ex::Basic; recurse::Bool=true)
    ex1 = Basic(expand_power_exp(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(expand_power_exp(BasicType(ex)))
    end
    ex1
end

function expand_power_exp(ex::BasicType{Val{:Pow}})
    as = get_args(ex)
    if get_symengine_class(as[2]) == :Add
        bs = get_args(as[2])
        trms = [as[1]^expand_power_exp(b) for b in bs]
        prod(trms)
    else
        as[1]^expand_power_exp(as[2])
    end
end

function expand_power_exp(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(expand_power_exp, as)...))
    end
end

## expand_power_base
## (x*y)^a --> x^a*y^a
function expand_power_base(ex::Basic; recurse::Bool=true)
    ex1 = Basic(expand_power_base(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(expand_power_base(BasicType(ex)))
    end
    ex1
end

function expand_power_base(ex::BasicType{Val{:Pow}})
    as = get_args(ex)
    if get_symengine_class(as[1]) == :Mul
        bs = get_args(as[1])
        trms = [b^expand_power_base(as[2]) for b in bs]
        prod(trms)
    else
        as[1]^expand_power_base(as[2])
    end
end

function expand_power_base(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(expand_power_base, as)...))
    end
end


## rewrite_trig
## express in sin, cos or tan (not csc, sec or cot)
function rewrite_trig(ex::Basic; recurse::Bool=true)
    ex1 = Basic(rewrite_trig(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(rewrite_trig(BasicType(ex)))
    end
    ex1
end

function rewrite_trig(ex::BasicType{Val{:Csc}})
    as = get_args(ex)
    1 / sin(map(rewrite_trig, as)...)
end

function rewrite_trig(ex::BasicType{Val{:Sec}})
    as = get_args(ex)
    1 / cos(map(rewrite_trig, as)...)
end

function rewrite_trig(ex::BasicType{Val{:Cot}})
    as = get_args(ex)
    1 / tan(map(rewrite_trig, as)...)
end

function rewrite_trig(ex::BasicType{Val{:Csch}})
    as = get_args(ex)
    1 / sinh(map(rewrite_trig, as)...)
end

function rewrite_trig(ex::BasicType{Val{:Sech}})
    as = get_args(ex)
    1 / cosh(map(rewrite_trig, as)...)
end

function rewrite_trig(ex::BasicType{Val{:Coth}})
    as = get_args(ex)
    1 / tanh(map(rewrite_trig, as)...)
end

function rewrite_trig(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(rewrite_trig, as)...))
    end
end


## expand_trig
## apply the sum or double angle identities,

## sin(a+b) = sin(a) cos(b) + sin(b) cos(a)
## cos(a + b) = cos(a) cos(b) - sin(a) sin(b)
## tan(a+b) = (tan(a) + tan(b)) / (1 - tan(a)*tan(b))

## sin(2a) = 2sin(a)cos(a)
## cos(2b) = cos(a)^2 - sin(a)^2
## tan(2a) = 2tan(a) / (1 - tan(a)^2)

## sin(a/2) = sqrt((1-cos(a))/2) (pm)
## cos(a/2) = sqrt((1+cos(a))/2) (pm)
## tan(a/2) = sin(a) / (1 + cos(a))

## hyperbolic too!

function expand_trig(ex::Basic; recurse::Bool=true)
    ex = rewrite_trig(ex, recurse=recurse)
    ex1 = Basic(expand_trig(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(expand_trig(BasicType(ex)))
    end
    ex1
end

function expand_trig(ex::BasicType{Val{:Sin}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)

    ## This is *not* perfect
    ## sin(a + b + c) won't expand... Need _2 match to grab b + c
    ## must treat * and + specially
    m = pattern_match(ex, sin(_1 + _2))
    if m.match
        a, b = m.matches[_1] , m.matches[_2]
        return sin(a)*cos(b) + sin(b) * cos(a)
    end

    m = pattern_match(ex, sin(2 * _1))
    if m.match
        a = m.matches[_1]
        return 2sin(a)*cos(a)
    end

    m = pattern_match(ex, sin(_1 / 2))
    if m.match
        a = m.matches[_1]
        return sqrt((1 - cos(a))/2)
    end

    return sin(expand_trig(arg))
    


    
    ## ## handle sum
    ## if ty == :Add
    ##     bs = get_args(arg)
    ##     a,b = bs[1], expand_trig(sum(bs[2:end]))
    ##     return sin(a)*cos(b) + sin(b)*cos(a)
    ## elseif ty == :Mul
    ##     bs = get_args(arg)
    ##     ts = map(get_symengine_class, bs)
    ##     ns = prod([t in (:Integer,:Rational, :Complex) ? b : Basic(1) for (t,b) in zip(ts, bs)])
    ##     notns = prod([!(t in (:Integer,:Rational, :Complex)) ? b : Basic(1) for (t,b) in zip(ts, bs)])
    ##     a = expand_trig(notns)
    ##     if ns == 2
    ##         return 2 * sin(a) * cos(a)
    ##     elseif ns == 1//2
    ##         return sqrt((1 - cos(a))/2)
    ##     else
    ##         return sin(ns * a)
    ##     end
    ## else
    ##     sin(expand_trig(arg))
    ## end
end


function expand_trig(ex::BasicType{Val{:Cos}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)

    ## This is *not* perfect
    ## cos(a + b + c) won't expand... Need _2 match to grab b + c
    ## must treat * and + specially
    m = pattern_match(ex, cos(_1 + _2))
    if m.match
        a, b = m.matches[_1] , m.matches[_2]
        return cos(a)*cos(b) - sin(a) * sin(b)
    end

    m = pattern_match(ex, cos(2 * _1))
    if m.match
        a = m.matches[_1]
        return cos(a)^2 - sin(a)^2
    end

    m = pattern_match(ex, cos(_1 / 2))
    if m.match
        a = m.matches[_1]
        return sqrt((1 + cos(a))/2)
    end

    return cos(expand_trig(arg))
    
    ## ## handle sum
    ## if ty == :Add
    ##     bs = get_args(arg)
    ##     a,b = bs[1], expand_trig(sum(bs[2:end]))
    ##     return cos(a) * cos(b) - sin(a) * sin(b)
    ## elseif ty == :Mul
    ##     bs = get_args(arg)
    ##     ts = map(get_symengine_class, bs)
    ##     ns = prod([t in (:Integer,:Rational, :Complex) ? b : Basic(1) for (t,b) in zip(ts, bs)])
    ##     notns = prod([!(t in (:Integer,:Rational, :Complex)) ? b : Basic(1) for (t,b) in zip(ts, bs)])
    ##     a = expand_trig(notns)
    ##     if ns == 2
    ##         return cos(a)^2 - sin(a)^2
    ##     elseif ns == 1//2
    ##         return sqrt((1 + cos(a))/2)
    ##     else
    ##         return cos(ns * a)
    ##     end
    ## else
    ##     cos(expand_trig(arg))
    ## end
        
end


function expand_trig(ex::BasicType{Val{:Tan}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)


    ## This is *not* perfect
    ## tan(a + b + c) won't expand... Need _2 match to grab b + c
    ## must treat * and + specially
    m = pattern_match(ex, tan(_1 + _2))
    if m.match
        a, b = m.matches[_1] , m.matches[_2]
        return (tan(a) + tan(b)) / (1 - tan(a) * tan(b))
    end

    m = pattern_match(ex, tan(2 * _1))
    if m.match
        a = m.matches[_1]
        return  2*tan(a) / (1 - tan(a)^2)
    end

    m = pattern_match(ex, tan(_1 / 2))
    if m.match
        a = m.matches[_1]
        return sin(a) / (1 + cos(a))
    end

    return tan(expand_trig(arg))
    
    
    ## ## handle sum
    ## if ty == :Add
    ##     bs = get_args(arg)
    ##     a,b = bs[1], expand_trig(sum(bs[2:end]))
    ##     return (tan(a) + tan(b)) / (1 - tan(a) * tan(b))
    ## elseif ty == :Mul
    ##     bs = get_args(arg)
    ##     ts = map(get_symengine_class, bs)
    ##     ns = prod([t in (:Integer,:Rational, :Complex) ? b : Basic(1) for (t,b) in zip(ts, bs)])
    ##     notns = prod([!(t in (:Integer,:Rational, :Complex)) ? b : Basic(1) for (t,b) in zip(ts, bs)])
    ##     a = expand_trig(notns)
    ##     if ns == 2
    ##         return 2*tan(a) / (1 - tan(a)^2)
    ##     elseif ns == 1//2
    ##         return sin(a) / (1 + cos(a))
    ##     else
    ##         return tan(ns * notns)
    ##     end
    ## else
    ##     tan(expand_trig(arg))
    ## end
end


function expand_trig(ex::BasicType{Val{:Sinh}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)
    
    ## handle sum
    if ty == :Add
        bs = get_args(arg)
        a,b = bs[1], expand_trig(sum(bs[2:end]))
        return sinh(a)*cosh(b) + sinh(b)*cosh(a)
    elseif ty == :Mul
        bs = get_args(arg)
        ts = map(get_symengine_class, bs)
        ns = prod([t in (:Integer,:Rational, :Complex) ? b : Basic(1) for (t,b) in zip(ts, bs)])
        notns = prod([!(t in (:Integer,:Rational, :Complex)) ? b : Basic(1) for (t,b) in zip(ts, bs)])
        a = expand_trig(notns)
        if ns == 2
            return 2 * sinh(a) * cosh(a)
        elseif ns == 1//2
            return sqrt((cosh(a)-1)/2)
        else
            return sinh(ns * a)
        end
    else
        sinh(expand_trig(arg))
    end
end


function expand_trig(ex::BasicType{Val{:Cosh}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)
    
    ## handle sum
    if ty == :Add
        bs = get_args(arg)
        a,b = bs[1], expand_trig(sum(bs[2:end]))
        return cosh(a) * cosh(b) + sinh(a) * sinh(b)
    elseif ty == :Mul
        bs = get_args(arg)
        ts = map(get_symengine_class, bs)
        ns = prod([t in (:Integer,:Rational, :Complex) ? b : Basic(1) for (t,b) in zip(ts, bs)])
        notns = prod([!(t in (:Integer,:Rational, :Complex)) ? b : Basic(1) for (t,b) in zip(ts, bs)])
        a = expand_trig(notns)
        if ns == 2
            return cosh(a)^2 + sinh(a)^2
        elseif ns == 1//2
            return sqrt((1 + cosh(a))/2)
        else
            return cosh(ns * a)
        end
    else
        cosh(expand_trig(arg))
    end
        
end

function expand_trig(ex::BasicType{Val{:Tanh}})
    arg = get_args(ex)[1]
    ty = get_symengine_class(arg)
    
    ## handle sum
    if ty == :Add
        bs = get_args(arg)
        a,b = bs[1], expand_trig(sum(bs[2:end]))
        return (tanh(a) + tanh(b)) / (1 + tanh(a) * tanh(b))
    elseif ty == :Mul
        bs = get_args(arg)
        ts = map(get_symengine_class, bs)
        ns = prod([t in (:Integer,:Rational, :Complex) ? b : Basic(1) for (t,b) in zip(ts, bs)])
        notns = prod([!(t in (:Integer,:Rational, :Complex)) ? b : Basic(1) for (t,b) in zip(ts, bs)])
        a = expand_trig(notns)
        if ns == 2
            return 2*tan(a) / (1 - tan(a)^2)
        elseif ns == 1//2
            return 2*sinh(a)*cos(a) / (2*cosh(a)^2 - 1)
        else
            return tanh(ns * notns)
        end
    else
        tanh(expand_trig(arg))
    end
end

function expand_trig(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(expand_trig, as)...))
    end
end





## ## how to pattern match
## ## This needs generalizing!!
## function pattern_match(x::Symbol)
##     function(ex)
##         get_symengine_class(ex) == x || return (false, nothing)
##         return(true, get_args(ex)[1])
##     end
## end

## function pattern_match_sq(x::Symbol)
##     function (ex)
##         get_symengine_class(ex) == :Pow || return (false, nothing)
##         as = get_args(ex)
##         get_symengine_class(as[1]) == x || return(false, nothing)
##         (get_symengine_class(as[2]) in (:Integer,:Rational)) && as[2] >= 2 || return(false, nothing)
##         return(true, get_args(as[1])[1])
##     end
## end

## function pattern_match_neg_sq(x::Symbol)
##     function (ex)
##         get_symengine_class(ex) == :Mul || return (false, nothing)
##         ## hack to check if neg
##         get_symengine_class(-ex) != :Mul || return(false, nothing)
##         ex = -ex
##         get_symengine_class(ex) == :Pow || return (false, nothing)
##         as = get_args(ex)
##         get_symengine_class(as[1]) == x || return(false, nothing)
##         (get_symengine_class(as[2]) in (:Integer,:Rational)) && as[2] >= 2 || return(false, nothing)
##         return(true, get_args(as[1])[1])
##     end
## end

## # matching sin(a)cos(b)
## function pattern_match_prod(x1::Symbol, x2::Symbol)
##     function(ex)
##         get_symengine_class(ex) == :Mul || return(false, nothing)
##         args = get_args(ex)
##         length(args) == 2 || return(false, nothing)
##         us = Bool[pattern_match(x1)(a)[1] for a in args]
##         vs = Bool[pattern_match(x2)(a)[1] for a in args]
##         any(us) && any(vs) || return(false, nothing)

##         return (true, (get_args(args[us][1])[1], get_args(args[vs][1])[1]))
##     end
## end


## function pattern_match_neg_prod(x1::Symbol, x2::Symbol)
##     function (ex)
##         pattern_match_prod(x1, x2)(-ex)
##     end
## end



## trigsimp
## 2sin(x)cos(x) -> sin(2x); 2sinh(x)cosh(x) -> sinh(2x)
## cos^2(x) - sin^2(x)


function trigsimp(ex::Basic; recurse::Bool=true)
    ex = rewrite_trig(ex, recurse=recurse)
    ex1 = Basic(trigsimp(BasicType(ex)))
    while recurse && ex1 != ex
        ex = ex1
        ex1 = Basic(trigsimp(BasicType(ex)))
    end
    ex1
end





function trigsimp(ex::BasicType{Val{:Mul}})
    ## sin(x) cos(x) -> sin(2x)/2
    out = pattern_match(ex, ___*sin(_1)*cos(_1))
    if out.match
        a = out.matches[_1]
        ex = ex / sin(a) / cos(a)
        ex = ex * sin(2*a) / 2
    end



    
    ##
    ## sinh(x) cosh(x) -> sinh(2x)/2
    out = pattern_match(ex, ___*sinh(_1)*cosh(_1))
    if out.match
        a = out.matches[_1]
        ex = ex / sinh(a) / cosh(a)
        ex = ex * sinh(2*a) / 2
    end

    ## others?

    
    ex

end



function trigsimp(ex::BasicType{Val{:XXX}})
    as = get_args(ex)

    ## cos(x)^2 - sin(x)^2  -> cos(2x)
    us = filter(u -> u[1], map(pattern_match_neg_sq(:Sin), as))
    vs = filter(u -> u[1], map(pattern_match_sq(:Cos), as))

    arg_us = [u[2] for u in us]
    arg_vs = [u[2] for u in vs]

    
    args = intersect(arg_us, arg_vs)

    for a in args
        ex = ex - cos(a)^2 + sin(a)^2
        ex = ex + cos(2*a)
    end

    ## -cos(x)^2 + sin(x)^2  -> -cos(2x)
    us = filter(u -> u[1], map(pattern_match_neg_sq(:Cos), as))
    vs = filter(u -> u[1], map(pattern_match_sq(:Sin), as))

    arg_us = [u[2] for u in us]
    arg_vs = [u[2] for u in vs]

    
    args = intersect(arg_us, arg_vs)

    for a in args
        ex = ex + cos(a)^2 - sin(a)^2
        ex = ex - cos(2*a)
    end


    ## cosh(x)^2 + sinh(x)^2  -> cosh(2x)
    us = filter(u -> u[1], map(pattern_match_sq(:Sinh), as))
    vs = filter(u -> u[1], map(pattern_match_sq(:Cosh), as))

    arg_us = [u[2] for u in us]
    arg_vs = [u[2] for u in vs]

    
    args = intersect(arg_us, arg_vs)

    for a in args
        ex = ex - cosh(a)^2 - sinh(a)^2
        ex = ex + cosh(2*a)
    end

    ## sin(a)cos(b) + sin(b)*cos(a) -> sin(a + b)
    us = filter(u -> u[1], map(pattern_match_prod(:Sin, :Cos), as))
    vs = filter(u -> u[1], map(pattern_match_prod(:Sin, :Cos), as))

    
    arg_us = [u[2] for u in us]
    arg_vs = map(reverse, [u[2] for u in vs])
    args = intersect(arg_us, arg_vs)

    ## make unique
    seen = Set()
    for a in args
        if !((a in seen) || (reverse(a) in seen))
            push!(seen, a)            
        end

    end

    for a in collect(seen)
        u, v = a
        ex = ex - sin(u)*cos(v) - sin(v)*cos(u)
        ex = ex + sin(u + v)
    end

    ## cos(a)cos(b) - sin(a)*sin(a) -> cos(a - b)
    us = filter(u -> u[1], map(pattern_match_prod(:Cos, :Cos), as))
    vs = filter(u -> u[1], map(pattern_match_neg_prod(:Sin, :Sin), as))
    
    arg_us = [sort(collect(u[2]), by=SymEngine.toString) for u in us]
    arg_vs = [sort(collect(u[2]), by=SymEngine.toString) for u in vs]
    println(us)
    println(arg_us)
    println(arg_vs)
    args = intersect(arg_us, arg_vs)
    println(args)
    for a in args
        u, v = a
        ex = ex - cos(u)*cos(v) + sin(v)*sin(u)
        ex = ex + cos(u + v)
    end
    
    ex

end

        
    


function trigsimp(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(trigsimp, as)...))
    end
end
