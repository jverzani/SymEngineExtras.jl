using Iterators

BasicType = SymEngine.BasicType
get_symengine_class(ex::Basic) = SymEngine.get_symengine_class(ex)
get_symengine_class(ex::BasicType) = get_symengine_class(Basic(ex))
get_args(ex::Basic) = SymEngine.get_args(ex)
get_args(ex::BasicType) = get_args(Basic(ex))



export pattern_match
export __, ___, _1, _2, _3, _4, _5, _6, _7, _8



const __ = symbols("__")
const _1, _2, _3, _4, _5, _6, _7, _8 = _vars = symbols("_1 _2 _3 _4 _5 _6 _7 _8")
const ___ = symbols("___") # slurp
const _allvars = (__, ___, _vars...)



"""
return (Bool, match) where
Bool; is true is match, false if not
match  is `nothing` or  the argument(s) that match the expression

## ```
## pattern_match("sin(cos(x))*cos(sin(x))", :Mul, ((:Sin, _), (:Cos, _))) -> (true, (cos(x), sin(x))))

## """


type PatternMatch
    match::Bool
    matches::Dict
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
        if k == ___
            if haskey(p.matches,k) push!(p.matches[k], q.matches[k]) else p.matches[k] = q.matches[k] end
            continue
        end
        p.matches[k] = q.matches[k]
    end
    return true
end


## Kinda like filter to extract matching expressions, but also return index
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

## what to pass down to matches!!
function pattern_match(ex::Basic, pat::Basic)
    p_op = get_symengine_class(pat)
    p_op == :Symbol && return PatternMatch(true, Dict(pat=>ex))
    
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
    if ___ in pas
        slurp = true
        pas = setdiff(pas, ___)
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
                op = get_symengine_class(ex) == :Mul ? prod : sum
                out.matches[___] = op(eas[is])
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
function check_exchangeable_pair(ex, pat1, pat2)
    
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
            
            return (true, (eas[i], eas[j], op == :Mul ? prod(rest) : sum(rest), da[_1], da[_2]))
        end
    end
    return(false, tuple())
end
 
