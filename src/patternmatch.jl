using Iterators

## Mull over
## variables of the form _x and x_
## the latter can beused to make replacement reach replace(sin(2x), sin(x_) => -cos(x)) would  match x_ with 2x and return -cos(2x). The point being x_ would use x as key
## this would not work in sympy, as we need to identify x_ with x and the only way I can think of would be: Basic(Symbolx(string(x)[1:end-1]))
## normalize(x) (endswith(string(x), "_") ? Basic(...) : x


## slurpvar -> variadic match: match 0,1,... terms in a sum or product

## TODO
## alloctions tuples, not dictionary?
## pass along dictionary?
## variadic
## tighten up
## rename get_symengine_class -> head
## get_arg -> args
## put in module
## export variables?




## Fix
#d = match(_1^_2*__1, x^y*1) # __1 => 1 should match


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

# zero or one
unit_value(ex::BasicType{Val{:Mul}}) = Basic(1)
unit_value(ex::BasicType{Val{:Add}}) = Basic(0)
unit_value(ex::Basic) = unit_value(BasicType(ex))



## We use "_var" for a place holder
## We use "__var" for a "slurper"

## TODO: add `phs` for pass in placeholders
const DEFAULT_PHS = Any[Set{Basic}()]

set_default_placeholders(set) = (DEFAULT_PHS[1] = set)

isplaceholder(x, phs=DEFAULT_PHS[1]) = startswith(string(x), "_") || endswith(string(x), "_") || in(x, phs)
isdontcare(x) = string(x) == "_ϕ"
isslurpvar(x) = startswith(string(x), "__") || endswith(string(x), "__")
isdontcareslurp(x) = string(x) == "__ϕ"





mutable struct PatternMatch{K,V}
    match::Bool
    matches::Dict{K,V}
end
PatternMatch(m::Bool) = PatternMatch(m, Dict{Basic, Basic}())

Base.ismatch(p::PatternMatch) = p.match
matches(p::PatternMatch) = p.matches
export matches

function Base.show(io::IO, p::PatternMatch)
    println(io, "Pattern matches: ", ismatch(p))
    if ismatch(p)
        for (k,v) in matches(p)
            println(io, "  ", k, " => ", v)
        end
    end
end

Base.:&(p::PatternMatch, q::PatternMatch) = ismatch(p) & ismatch(q)
Base.:|(p::PatternMatch, q::PatternMatch) = ismatch(p) | ismatch(q)

## true if match==match and _x vars are equal 
function Base.:(==)(p::PatternMatch, q::PatternMatch)
    ismatch(p) == ismatch(q)     || return false
    ismatch(p)                || return true # both false

    ## compare dicts
    #    pks = setdiff(collect(keys(matches(p))), __)
    #    qks = setdiff(collect(keys(matches(q))), __)
    pks = filter(!isslurpvar, collect(keys(matches(p))))
    qks = filter(!isslurpvar, collect(keys(matches(q))))
    
    
    length(pks) == length(qks) || return false
    for k in pks
        matches(p)[k] == matches(q)[k] || return false
    end
    true
end

# Are (k,v) in q all in p?
function Base.issubset(q::PatternMatch, p::PatternMatch)
    (!ismatch(p) || !ismatch(q)) && return false
    for (k, v) in matches(q)
        isdontcare(k) || isdontcareslurp(k) && continue
        if haskey(matches(p), k)
            matches(p)[k] == v || return false
        end
    end
    true
end

## do dictionaries p q match where they have common keys
function isconsistent(p::Dict, q::Dict)
    common_keys = intersect(keys(p), keys(q))
    for k in common_keys
        p[k] == q[k] || return false
    end
    return true
end
isconsistent(p::PatternMatch, q::PatternMatch) = (ismatch(p)==ismatch(q) && isconsistent(matches(p), matches(q)))
## does q agree with p where commonly defined? If so, return true *and* mutate p
## agree discounts __ value 
function agree!(p::PatternMatch, q::PatternMatch)
    (!ismatch(p) || !ismatch(q)) && return false

    # check values in q match values in p or return false
    #!issubset(q, p) && return false
    !isconsistent(q, p) && return false

    # now update values in p for keys in q but not p
    for (k,v) in matches(q)
        isdontcare(k) && continue
        if isslurpvar(k)
            if haskey(matches(p),k)
                push!(p.matches[k], v)
            else
                p.matches[k] = v
            end
            continue
        end
        p.matches[k] = v
    end

    return true
end

## what to pass down to matches!!
function pattern_match(ex::Basic, pat::Basic, phs=DEFAULT_PHS[1])
    p_op = get_symengine_class(pat)
    ## symbols are special
    if p_op == :Symbol
        #pat in _allvars && return PatternMatch(true, Dict(pat=>ex))
        isplaceholder(pat, phs) && return PatternMatch(true, Dict(pat=>ex))        
        ex == pat && return PatternMatch(true)
        return PatternMatch(false)
    end

    pattern_match(BasicType(ex), pat, phs)
end


function pattern_match(ex::Union{BasicType{Val{:Mul}}, BasicType{Val{:Add}}}, pat, phs=DEFAULT_PHS[1])
    ## what to do
    op = get_symengine_class(Basic(ex))
    p_op = get_symengine_class(pat)

    op != p_op && return PatternMatch(false)

    eas, pas = get_args(Basic(ex)), get_args(pat)      
    sort!(eas, by=SymEngine.toString)
    
    slurp = false
    slurpingwith = filter(isslurpvar, pas) #collect(filter(var -> var in pas, __slurpvars))
    length(slurpingwith) > 1 && return throw(ArgumentError("Too many slurping variables"))
    if length(slurpingwith) == 1
        slurp = true
        pas = setdiff(pas, slurpingwith)
        slurpvar = slurpingwith[1]
    end
    

    (length(eas) < length(pas)) || slurp || length(eas) == length(pas) || return PatternMatch(false)

    

    ## need to ensure we don't consider cases where we match same thing!
    d = Dict{Basic, Basic}()
    matched_terms = Basic[]
    
    for p in pas
        found_match=false
        for expr in eas
            expr in matched_terms && continue
            pm = match(p, expr)
            if ismatch(pm)

                push!(matched_terms, expr)
                isconsistent(d, matches(pm)) || return PatternMatch(false)
                merge!(d, matches(pm))
                found_match=true
                break
            end
        end
        !found_match && return PatternMatch(false)
    end

    # handle slurping variables!
    if slurp
        not_matched = setdiff(eas, matched_terms)
        if length(not_matched) > 0
            d[slurpvar] = prod_sum(ex)(not_matched) 
        else
            d[slurpvar] = unit_value(ex)
        end
    end

    return PatternMatch(true,d)

    # ## we check M x N
    # d = Dict()
    # for p in pas
    #     d[p] = cases(eas, p, phs)
    # end
    
    # c = tuple()
    # for case in product([d[k] for k in keys(d)]...)
    #     out = case[1][1]
    #     a = true
    #     s = Set(case[1][2])
    #     for c in case[2:end]
    #         u, i = c
    #         if i in s
    #             a = false
    #             break
    #         end
    #         push!(s, i)
            
    #         a = agree!(out, u)
    #         a || continue
    #     end
    #     if a
    #         ## if slurp, well we slurp up other variables
    #         if slurp
    #             is = [c[2] for c in case]
    #             is = setdiff(1:length(eas), is)
    #             out.matches[slurpingwith[1]] = prod_sum(ex)(eas[is])
    #         end
    #         return out
    #         break
    #     end
    # end

    return PatternMatch(false)
    
end

function pattern_match(ex::SymEngine.BasicType, pat, phs=DEFAULT_PHS[1])
    ex = Basic(ex)
    op = get_symengine_class(ex)
    p_op = get_symengine_class(pat)

    if p_op in [:Integer, :Rational, :Complex]
        ex != pat && return PatternMatch(false)
        return PatternMatch(true)
    end

    if p_op == :Symbol
        #        if pat in _allvars
        if isplaceholder(pat, phs)
            out = PatternMatch(true)

            
            agree!(out, PatternMatch(true, Dict(pat => ex)))
            return out
        else
            return PatternMatch(ex == pat)
        end
    end

    ## recurse through arguments
    eas, pas = get_args(ex), get_args(pat)
    
    ## Special case
    ## Handle slurpvars so that x ~ _1 + __1 will yield (_1 => x, __1 => 0)
    ## and x ~ _1 * __1 will yield (_1 => x, __1 => 1)
    ## even though expressions don't match at the op level. 
    if p_op in [:Mul, :Add]
        slurpvars = filter(isslurpvar, pas)
        if length(slurpvars) > 0 && length(pas) - length(slurpvars) == 1
            pm = pattern_match(ex, setdiff(pas, slurpvars)[1])
            agree!(pm, PatternMatch(true, Dict(slurpvar=> p_op==:Mul ? Basic(1) : Basic(0) for slurpvar in slurpvars)))
            return pm
        end
    end

    if p_op in [:Pow] && isslurpvar(pas[2]) && op != :Pow
        pm = pattern_match(ex, pas[1])
        agree!(pm, PatternMatch(true, Dict(pas[2] => 1)))
        return pm
    end
                                

    
    op !== p_op && return PatternMatch(false)

    if op in [:Add, :Mul]
        sort!(eas, by=SymEngine.toString) ## makes some things work... (_1*_2 + _1*_3 depends on sort order when matching)
    end

    length(eas) < length(pas) && return PatternMatch(false)

    ## need to consider different orders

    out = PatternMatch(true)
    for (e,p) in zip(eas, pas)

        if !agree!(out, pattern_match(e, p, phs))
            return PatternMatch(false)
        end
    end
    
    return out
end

## there is an issue with patterns like sin(_1)*sin(_2) - cos(_2)*cos(_1)
## there is no guarantee what term gets labeled sin(_1)*sin(_2) so comparing _2 across pieces
## of the pattern is not good.
## this handles this case, though should be generalized. However, note that there is n! checking (n=subpatterns)
function _check_exchangeable_pair(ex, pat1, pat2, phs=DEFAULT_PHS[1])
    
    eas = SymEngine.get_args(Basic(ex))
    op = SymEngine.get_symengine_class(Basic(ex))
    
    n = length(eas)
    
    c1 = cases(eas, pat1, phs)
    c2 = cases(eas, pat2, phs)

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

   `match(pattern, expression, phs=DEFAULT_PHS[1])`: return `PatternMatch` object


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

In a picture, we might see

```
    sin
     |
    pow 
    /  \     
   sum   2
  /  | \ 
 pow x  1
 / \
x   2
```


An expression will match a pattern if the two expression trees are
identical, unless the pattern has a wildcard. For most operations, a
wild card simply matches any subtree. Wildcards have fixed names `_1`,
`_2`, ....

So the pattern `sin(_1)` will match `sin((x^2 + 2 + 1)^2)`
as the function heads match and the `_1` matches the subtree starting from `pow`.
Similarly, `sin(_1^2)` will match, with `_1`
matching `x^2 + x + 1`,  the power function matches the exponent
matches and the wild card  matches the subtree from `sum`. The pattern `sin((x^2 + x + 1)^_1)` will also match, as the `_1` will
match the exponent `2`. However, `sin(_1^3)` will not match -- the `3`
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
Base.match(pat::Basic, ex::Basic, phs=DEFAULT_PHS[1]) = pattern_match(ex, pat, phs)



"""

    `ismatch(pattern, expression)`: does pattern match expression *or* subexpression?

Example
```
ismatch(x, sin(x))  # true, as `x` matches subexpression `x`
ismatch(x^2, sin(x))  # false
ismatch(x^2, sin(x^2*cos(x)))  # true, will match the `x^2` in the argument.

"""
function Base.ismatch(pat, ex, phs=DEFAULT_PHS[1])
    pattern_match(ex, pat, phs).match && return true

    exs = SymEngine.get_args(ex)
    any([ismatch(pat, ex, phs) for ex in exs]) && return true

    return false
end



"""

    cases(expessions, pattern)

Return patternmatches for matches expression and indices of matched expressions

Examples:
    
```
pms, inds = cases([x, x^2, x^3], x^_1) # inds = [2,3], pms = [pattern_match(x^2, x^_1), pattern_match(x^3, x^_1)]
```

Kinda like filter to extract matching expressions, but also returns index relative to original expressions
"""
function cases(exs::Vector, pat, phs=DEFAULT_PHS[1])
    ## return cases and their indices
    es = PatternMatch[]
    ind = Int[]
    for i in 1:length(exs)
        a = pattern_match(exs[i], pat, phs) 
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

    exs = get_args(ex)
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


##
## replace
## rewrite(sin(x)*cos(y), sin(_1)*cos(_2)*__1,(sin(_1+_2) + cos(_1-_2))*__1)
function rewrite(ex, pat, rpat)
    p = match(pat, ex)

    !ismatch(p) && return ex
    subs(rpat, matches(p)...)
end
        
    
