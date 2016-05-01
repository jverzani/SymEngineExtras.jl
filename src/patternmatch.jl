using Iterators

## need to check __ and ___ consoliate?


BasicType = SymEngine.BasicType
get_symengine_class(ex::Basic) = SymEngine.get_symengine_class(ex)
get_symengine_class(ex::BasicType) = get_symengine_class(Basic(ex))
get_args(ex::Basic) = SymEngine.get_args(ex)
get_args(ex::BasicType) = get_args(Basic(ex))

## common pattern: extract operator for these two
prod_sum(ex::BasicType{Val{:Mul}}) = prod
prod_sum(ex::BasicType{Val{:Add}}) = sum
prod_sum(ex::Basic) = prod_sum(BasicType(ex))

export __, _1, _2, _3, _4, _5, _6, _7, _8
export ___, __1, __2, __3, __4, __5, __6, __7, __8



const __ = symbols("__")
const _1, _2, _3, _4, _5, _6, _7, _8 = _vars = symbols("_1 _2 _3 _4 _5 _6 _7 _8")
const ___, __1, __2, __3, __4, __5, __6, __7, __8 = __slurpvars = symbols("___ __1 __2 __3 __4 __5 __6 __7 __8")
const _allvars = (__, ___, _vars..., __slurpvars...)



type PatternMatch
    match::Bool
    matches::Dict
end

function Base.show(io::IO, p::PatternMatch)
    println(io, "Pattern matches: ", p.match)
    p.match && println(io, p.matches)
end

Base.(:&)(p::PatternMatch, q::PatternMatch) = p.match & q.match
Base.(:|)(p::PatternMatch, q::PatternMatch) = p.match | q.match
## true if match==match and _x vars are equal 
function Base.(:(==))(p::PatternMatch, q::PatternMatch)
    p.match == q.match     || return false
    p.match                || return true # both false
    ## compare dicts
    pks = setdiff(collect(keys(p.matches)), __)
    qks = setdiff(collect(keys(q.matches)), __)
    length(pks) == length(qks) || return false
    for k in pks
        p.matches[k] == q.matches[k] || return false
    end
    true
end

## does q agree with p where commonly defined? If so, return true *and* mutate p
## agree discounts __ value 
function agree!(p::PatternMatch, q::PatternMatch)
    (!p.match || !q.match) && return false
    
    for k in keys(q.matches)
        k == __ || k == ___ && continue
        if haskey(p.matches, k)
            p.matches[k] == q.matches[k] || return false
        end
    end
    for k in keys(q.matches)
        k == __ && continue
        if k in __slurpvars
            if haskey(p.matches,k) push!(p.matches[k], q.matches[k]) else p.matches[k] = q.matches[k] end
            continue
        end
        p.matches[k] = q.matches[k]
    end
    return true
end

## what to pass down to matches!!
function pattern_match(ex::Basic, pat::Basic)
    p_op = get_symengine_class(pat)
    ## symbols are special
    if p_op == :Symbol
        pat in _allvars && return PatternMatch(true, Dict(pat=>ex))
        ex == pat && return PatternMatch(true, Dict())
        return PatternMatch(false, Dict())
    end
    
    pattern_match(BasicType(ex), pat)
end


function pattern_match(ex::Union{BasicType{Val{:Mul}}, BasicType{Val{:Add}}}, pat)
    ## what to do
    op = get_symengine_class(Basic(ex))
    p_op = get_symengine_class(pat)

    op != p_op && return PatternMatch(false, Dict())

    eas, pas = get_args(Basic(ex)), get_args(pat)      
    sort!(eas, by=SymEngine.toString)
    
    slurp = false
    slurpingwith = collect(filter(var -> var in pas, __slurpvars))
    length(slurpingwith) > 1 && return throw(ArgumentError("Too many slurping variables"))
    if length(slurpingwith) == 1
        slurp = true
        pas = setdiff(pas, __slurpvars)
    end

    slurp || length(eas) == length(pas) || return PatternMatch(false, Dict())

    
    ## we check M x N
    d = Dict()
    for p in pas
        d[p] = cases(eas, p)
    end

    ## need to ensure we don't consider cases where we match same thing!
    c = tuple()
    for case in product([d[k] for k in keys(d)]...)
        out = case[1][1]
        a = true
        s = Set(case[1][2])
        for c in case[2:end]
            u, i = c
            if i in s
                a = false
                break
            end
            push!(s, i)
            
            a = agree!(out, u)
            a || continue
        end
        if a
            ## if slurp, well we slurp up other variables
            if slurp
                is = [c[2] for c in case]
                is = setdiff(1:length(eas), is)
                out.matches[slurpingwith[1]] = prod_sum(ex)(eas[is])
            end
            return out
            break
        end
    end

    return PatternMatch(false, Dict())
    
end

function pattern_match(ex::SymEngine.BasicType, pat)
    ex = Basic(ex)
    op = get_symengine_class(ex)
    p_op = get_symengine_class(pat)

    if p_op in [:Integer, :Rational, :Complex]
        ex != pat && return PatternMatch(false, Dict())
        return PatternMatch(true, Dict())
    end

    if p_op == :Symbol
        if pat in _allvars
            out = PatternMatch(true, Dict())
            agree!(out, PatternMatch(true, Dict(pat => ex)))
            return out
        else
            return PatternMatch(ex == pat,  Dict())
        end
    end

    ## recurse through arguments
    op !== p_op && return PatternMatch(false, Dict())
    eas, pas = get_args(ex), get_args(pat)

    if op in [:Add, :Mul]
        sort!(eas, by=SymEngine.toString) ## makes some things work... (_1*_2 + _1*_3 depends on sort order when matching)
    end

    length(eas) < length(pas) && return PatternMatch(false, Dict())

    ## need to consider different orders

    out = PatternMatch(true, Dict())
    for (e,p) in zip(eas, pas)
#        println(e, " ~ ", p)
        if !agree!(out, pattern_match(e, p))
            return PatternMatch(false, Dict())
        end
    end
    return out
end

## there is an issue with patterns like sin(_1)*sin(_2) - cos(_2)*cos(_1)
## there is no guarantee what term gets labeled sin(_1)*sin(_2) so comparing _2 across pieces
## of the pattern is not good.
## this handles this case, though should be generalized. However, note that there is n! checking (n=subpatterns)
function _check_exchangeable_pair(ex, pat1, pat2)
    
    eas = SymEngine.get_args(Basic(ex))
    op = SymEngine.get_symengine_class(Basic(ex))
    
    n = length(eas)
    
    c1 = cases(eas, pat1)
    c2 = cases(eas, pat2)

    for case in product(c1, c2)
        pma, i = case[1]
        pmb, j = case[2]
        i == j && continue # next case
        da, db = pma.matches, pmb.matches
        if (da[_1] == db[_1] && da[_2] == db[_2]) ||
            (da[_1] == db[_2] && da[_2] == db[_1])
            ## a match
            rest = eas[setdiff(1:n, [i,j])]
            
            return (true, (eas[i], eas[j], prod_sum(ex)(rest), da[_1], da[_2]))
        end
    end
    return(false, tuple())
end
 

##


##################################################

## interfaces

## main function

"""

   `match(pattern, expression)`: return `PatternMatch` object


Pattern matching.

Matching *basically* follows rules laid out for [ginac](http://www.ginac.de/tutorial/#Pattern-matching-and-advanced-substitutions).

An expression has a symbolic representation in terms of a
[tree](http://docs.sympy.org/dev/tutorial/manipulation.html).
The `SymPy` docs are clearer, but for now
consider `sin((x^2+x + 1)^2)`. The function `sin` has an
argument `x^2` which in turn is the power operation with arguments
`x^2 + x` and `2`. The `2` is a leaf on the tree, but we can write
`x^2+x+1` as the `sum` of three arguments, `x^2`, `x`, and `1`. Again,
`1` is a leaf, `x` -- a symbol -- is also leaf of the tree, but `x^2`
can be written as the power function with two argumentx `x` and `2`.

An expression will match a pattern if the two expression trees are
identical, unless the pattern has a wildcard. For most operations, a
wild card simply matches any subtree. Wildcards have fixed names `_1`,
`_2`, .... So the pattern `sin(_1)` will match `sin((x^2 + 2 + 1)^2)`
as the function heads match and the wild card stops the matches at the
arguments. The pattern `sin((x^2 + x + 1)^_1)` will also match, as the
`_1` will match the exponent `2`. Similarly, `sin(_1^2)` will match, with `_1`
matching `x^2 + x + 1`. However, `sin(_1^3)` will not match -- the `3`
does not match the `2`.

The term `x^2 + x + 1` can be matched by `_1`. But will it match `x^2
+ _1`? Well, here the answer is `no`. We assume `_1` matches a subtree
and `x+1` is two branches of the tree. For this purpose we have
`slurping` variables `__1` (two underscores for 3 characters). So `x^2
+ __1` will match. Slurping variables really only make sense for
addition and multiplication, but can be used elsewhere.

When a wild card is used more than once in a pattern, it must match
the same subtree. So `_1^_1` will match `(x+y)^(x+y)` but not
`x^(x+y)`. The special wildcard `__` can be used in the case where the
value can change from place to place.

Products and sums are different, in that there can 2 or more arguments
and these can be represented in the expression tree in an
unpredictable way.


# return value

If the pattern does not match the expression, a `PatternMatch` object is returned with the `match` field being `false`.

If `pattern` matches expression then a `PatternMatch` object is returned with `match=true` and `matches` a dictionary showing how
the wild cards matched.


Examples
```
match(sin(_1), sin(x)) # true with _1 => x
match(sin(_1), sin(cos(x))) # true with _1 => cos(x)
```

"""
Base.match(pat::Basic, ex::Basic) = pattern_match(ex, pat)



"""

    `ismatch(pattern, expression)`: does pattern match expression *or* subexpression?

Example
```
ismatch(x, sin(x))  # true, as `x` matches subexpression `x`
ismatch(x^2, sin(x))  # false
ismatch(x^2, sin(x^2*cos(x)))  # true, will match the `x^2` in the argument.

"""
function Base.ismatch(pat, ex)
    pattern_match(ex, pat).match && return true

    exs = SymEngine.get_args(ex)
    any([ismatch(pat, ex) for ex in exs]) && return true

    return false
end



"""

    `cases(expessions, pattern)` return patternmatches for matches expression and indices of matched expressions

Examples
```
pms, inds = cases([x, x^2, x^3], x^_1) # inds = [2,3], pms = [pattern_match(x^2, x^_1), pattern_match(x^3, x^_1)]
```

Kinda like filter to extract matching expressions, but also return index
 return filtered matches, index relative to original expressions
"""
function cases(exs::Vector, pat)
    ## return cases and their indices
    es = PatternMatch[]
    ind = Int[]
    for i in 1:length(exs)
        a = pattern_match(exs[i], pat) 
        if a.match
            push!(es, a)
            push!(ind, i)
        end
    end
    zip(es, ind)
end
export cases

"""

    `find(expression, pattern)` return subexpressions of `ex` that match `pattern` as a `Set`.

Returns a set of matched subexpressions.

Examples
```
find(x + x^2 + x^3, x)      # { x }, as x does not match x^2 or x^3
find(x + x^2 + x^3, x^_1)   # {x^2, x^3}
find(a*sin(x) + a*sin(y) + b*sin(x) + b*sin(y), sin(_1))  # {sin(x), sin(y)}, matches all four, but a set is returned.
```

"""
function Base.find(ex::Basic, pat, s = Set())
    match(pat, ex).match && push!(s, ex)

    exs = SymEngine.get_args(ex)
    for ex in exs
        find(ex, pat, s)
    end

    s
end
    



"""

    `replaceall(ex, lhs => rhs)`: uses lhs as pattern. For each match of pattern, replace with `rhs` which may involve wildcards expressions.

Examples
```
replaceall(sin(x), sin(_1) => sin(y))         # sin(y)
replaceall(a^2+b^2+(x+y)^2 +c, _1^2=>_1^3)    # a^3 + b^3 + (x + y)^3 + c
replaceall(sin(1+sin(x)), sin(_1)=>cos(_1))   # cos(1 + cos(x)) as recursively defined
replaceall(x^2 + x^3, _1^_2 => _1^(2*_2))     # x^4 + x^6
```

"""
function replaceall(ex, ps::Pair...)
    replaceall(BasicType(ex), ps...)
end
export replaceall



function replaceall(ex::Union{BasicType{Val{:Mul}},BasicType{Val{:Add}}},
                    ps::Pair...)
    exs = SymEngine.get_args(Basic(ex))
    ex = (prod_sum(ex))([replaceall(ex,  ps...) for ex in exs])

    for p in ps
        pat, rhs = p
        m = pattern_match(ex, pat)
        !m.match && continue
        ## now substitute
        for (k,v) in m.matches
            rhs = subs(rhs, k, v)
        end
        ex = rhs
    end
    ex
end

## recurse through so that
# subs(sin(1+sin(x)), sin(_1)=>cos(_1))  # cos(1 + cos(x)) and not cos(1 + sin(x))
# expand(replaceall(a*sin(x+y)^2+a*cos(x+y)^2+b,cos(_1)^2=>1-sin(_1)^2))  # a+.b
function replaceall(ex::BasicType, ps::Pair...)
    ## recursively call, then do top-level
    fn = SymEngineExtras.get_fun(ex)
    ex = Basic(ex)
    args = SymEngine.get_args(ex)
    if length(args) > 0
        ex = eval(Expr(:call, fn, [replaceall(arg, ps...) for arg in args]...))
    end
    for p in ps
        pat, rhs = p
        m = pattern_match(Basic(ex), pat)
        !m.match && continue
        ## now substitute
        for (k,v) in m.matches
            rhs = subs(rhs, k, v)
        end
        ex = rhs
    end

    ex
end
