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

    ## a log(b) -> log(b^a)
    m = pattern_match(ex, _1 * log(_2))
    if m.match
        a, b = [get(m.matches, k, Basic(1)) for k in (_1, _2)]
        return log(b^a)
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
    ## x^(ax) -> (x^a)^x
    m = pattern_match(ex, _1^(_2*___))
    if m.match
        a,b,c = [get(m.matches, k , Basic(1)) for k in (_1, _2, ___)]
        ex = (a^b)^c
    end

    ex
end

    
## 
function powsimp(ex::BasicType{Val{:Mul}})
    # x^n * y^n -> (x*y)^n
    out = pattern_match(ex, _1^_2 * _3^2 * ___)
    if out.match
        a,b,n,c = [get(out.matches, k, Basic(1)) for k in (_1, _3, _2, ___)]
        ex = (a * b)^n * c
    end

    out = pattern_match(ex, _1^2 * _1^_3 * ___)
    if out.match
        a,n,m,c = [get(out.matches, k, Basic(1)) for k in (_1, _2, _3, ___)]
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
    out = pattern_match(ex, _1^(_2 + _3 + ___))
    if out.match
        x,a,b,c = [get(out.matches, k, Basic(0)) for k in (_1, _2, _3, ___)]
        b = b + c
        a, b = map(expand_power_exp, (a,b))
        ex = x^a * x^b
    end
    ex
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
    out = pattern_match(ex, (_1 *_2)^_3)
    if out.match
        x,y,a = [get(out.matches, k, Basic(1)) for k in (_1, _2, _3)]
        ex = x^a * y^a
    end
    ex
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
    m = pattern_match(ex, sin(_1 + _2 + ___))
    if m.match
        a, b, c =[get(m.matches, k, Basic(0)) for k in (_1, _2, ___)]
        b = b + c
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

    arg = get_args(ex)[1]
    return sin(expand_trig(arg))
    
end


function expand_trig(ex::BasicType{Val{:Cos}})
    m = pattern_match(ex, cos(_1 + _2 + ___))
    if m.match
        a, b = [get(m.matches, k, Basic(0)) for k in (_1, _2, ___)]
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

    arg = get_args(ex)[1]
    return cos(expand_trig(arg))
    
end


function expand_trig(ex::BasicType{Val{:Tan}})
    m = pattern_match(ex, tan(_1 + _2 + ___))
    if m.match
        a, b, c = [get(m.matches, k, Basic(0)) for k in (_1, _2, ___)]
        b = b + c
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

    arg = get_args(ex)[1]    
    return tan(expand_trig(arg))
    
end


function expand_trig(ex::BasicType{Val{:Sinh}})

    m = pattern_match(ex, sinh(_1 + _2 + ___))
    if m.match
        a, b, c =[get(m.matches, k, Basic(0)) for k in (_1, _2, ___)]
        b = b + c
        return sinh(a)*cosh(b) + sinh(b) * cosh(a)
    end

    m = pattern_match(ex, sinh(2 * _1))
    if m.match
        a = m.matches[_1]
        return 2sinh(a)*cosh(a)
    end

    m = pattern_match(ex, sinh(_1 / 2))
    if m.match
        a = m.matches[_1]
        return sqrt((cosh(a) - 1)/2)
    end

    arg = get_args(ex)[1]
    return sinh(expand_trig(arg))
end

# https://en.wikipedia.org/wiki/Hyperbolic_function
function expand_trig(ex::BasicType{Val{:Cosh}})

    m = pattern_match(ex, cosh(_1 + _2 + ___))
    if m.match
        a, b, c =[get(m.matches, k, Basic(0)) for k in (_1, _2, ___)]
        b = b + c
        return sinh(a)*cosh(b) + sinh(b) * cosh(a)
    end

    m = pattern_match(ex, cosh(2 * _1))
    if m.match
        a = m.matches[_1]
        return cosh(a)^2 + sinh(a)^2
    end

    m = pattern_match(ex, cosh(_1 / 2))
    if m.match
        a = m.matches[_1]
        return sqrt((cosh(a) + 1)/2)
    end

    arg = get_args(ex)[1]
    return cosh(expand_trig(arg))
end
   

function expand_trig(ex::BasicType{Val{:Tanh}})

    m = pattern_match(ex, tanh(_1 + _2 + ___))
    if m.match
        a, b, c = [get(m.matches, k, Basic(0)) for k in (_1, _2, ___)]
        b = b + c
        return (tanh(a) + tanh(b)) / (1 + tanh(a) * tanh(b))
    end

    m = pattern_match(ex, tanh(2 * _1))
    if m.match
        a = m.matches[_1]
        return  2*tanh(a) / (1 + tanh(a)^2)
    end

    m = pattern_match(ex, tanh(_1 / 2))
    if m.match
        a = m.matches[_1]
        return (exp(x) - 1) / (exp(x) + 1)
    end

    arg = get_args(ex)[1]    
    return tan(expand_trig(arg))
    
end

function expand_trig(ex::BasicType)
    as = get_args(ex)
    if length(as) == 0
        return ex
    else
        eval(Expr(:call, get_fun(ex), map(expand_trig, as)...))
    end
end





## trigsimp
## 2sin(x)cos(x) -> sin(2x); 2sinh(x)cosh(x) -> sinh(2x)
## cos^2(x) - sin^2(x)


function trigsimp(ex::Basic; recurse::Bool=true)
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
        a, c = [get(out.matches, k, Basic(0)) for k in (_1,  ___)]
        a, c = map(trigsimp, (a,c))
        ex = c * sin(2a) / 2
    end

    ##
    ## sinh(x) cosh(x) -> sinh(2x)/2
    out = pattern_match(ex, ___*sinh(_1)*cosh(_1))
    if out.match
        a,c =  [get(out.matches, k, Basic(1)) for k in (_1,  ___)]
        a, c = map(trigsimp, (a,c))        
        ex = c * sinh(2a)/2
    end

    ## others?
    ex
end



function trigsimp(ex::BasicType{Val{:Add}})
    ## sin(a)cos(b) + sin(b)*cos(a) -> sin(a + b)
    out = pattern_match( ex, sin(_1)*cos(_2) + sin(_2)*cos(_1) + ___)
    if out.match
        a,b,c = [get(out.matches, k, Basic(0)) for k in (_1, _2, ___)]
        a, b, c = map(trigsimp, (a,b,c))                
        ex = c + sin(a+b)
    end


    ## cos(a)cos(b) - sin(a)*sin(a) -> cos(a - b)
    out = pattern_match( ex, cos(_1)*cos(_2) - sin(_1)*sin(_2))
    if out.match
        a,b,c = [get(out.matches, k, Basic(0)) for k in (_1, _2, ___)]
        a, b, c = map(trigsimp, (a,b,c))                        
        ex = c + cos(a+b)
    end
    

    ## cos(x)^2 - sin(x)^2  -> cos(2x)
    out = pattern_match( ex, cos(_1)^2 - sin(_1)^2 + ___)
    if out.match
        a,c = [get(out.matches, k, Basic(0)) for k in (_1,  ___)]
        ex = c + cos(2a)
    end

    ## -cos(x)^2 + sin(x)^2  -> -cos(2x)
    out = pattern_match( ex, -cos(_1)^2 + sin(_1)^2 + ___)
    if out.match
        a,c = [get(out.matches, k, Basic(0)) for k in (_1,  ___)]
        ex = c - cos(2a)
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
