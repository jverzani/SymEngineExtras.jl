BasicType = SymEngine.BasicType
get_symengine_class(ex::Basic) = SymEngine.get_symengine_class(ex)
get_symengine_class(ex::BasicType) = get_symengine_class(Basic(ex))
get_args(ex::Basic) = SymEngine.get_args(ex)
get_args(ex::BasicType) = get_args(Basic(ex))

get_fun(ex::BasicType{Val{:Add}}) = :(+)
get_fun(ex::BasicType{Val{:Sub}}) = :(-)
get_fun(ex::BasicType{Val{:Mul}}) = :(*)
get_fun(ex::BasicType{Val{:Div}}) = :(/)
get_fun(ex::BasicType{Val{:Pow}}) = :(^)
function get_fun(ex::BasicType)
    as = get_args(ex)
    fn = get_symengine_class(ex) |> string |> lowercase |> symbol
    fn
end




export pattern_match
export __, ___, _1, _2, _3, _4, _5, _6, _7, _8



const __ = symbols("__")
const _1, _2, _3, _4, _5, _6, _7, _8 = _vars = symbols("_1 _2 _3 _4 _5 _6 _7 _8")
const _allvars = (__, _vars...)
const ___ = symbols("___") # slurp
const _slurpvars = (___, )

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

## what to pass down to matches!!
function pattern_match(ex, pat, matches=Dict())

    get_symengine_class(ex) == get_symengine_class(pat)  || return PatternMatch(false, Dict())
    
    eas, pas = get_args(ex), get_args(pat)
    out = _match_args(eas, pas, matches, get_symengine_class(ex))

    ## for Mul and Add we need to consider commutivity!
    if !out.match
        op = get_symengine_class(ex)
        if op in (:Mul, :Add)
            peas = permutations(eas)
            for pe in peas
                newmatches = Dict()
                out = _match_args(pe, pas, newmatches, op)
                if out.match
                    ## break if newmatches agrees with matches
                    dobreak = true
                    for k in keys(newmatches)
                        k in (__, ___) && continue
                        if haskey(matches, k)
                            matches[k] == newmatches[k] && continue
                            dobreak = false
                            break
                        end
                    end
                    if dobreak
                        merge!(matches, newmatches)
                        return PatternMatch(true, matches)
                    end
                end
            end
        end
    end

    if out.match
        return out
    else
        return PatternMatch(false, Dict())
    end
end

function _match_args(eas, pas, matches, op=:_)
    ## reduce eas to match ___
    length(eas) < length(pas) - 1 && return PatternMatch(false, Dict())

    if length(eas) == length(pas) - 1  # drop slurping variable
        inds = [p in _slurpvars for p in pas]
        sum(inds) == 0 && return  PatternMatch(false, Dict())
        sum(inds) > 1 && throw(ArgumentError("too many slurping variables at this level"))
        pas = pas[filter(i -> !inds[i], 1:length(inds))]
    end

    ## now slurp. There *must* be a cleaner way to do this
    if length(eas) > length(pas)
        inds = [p in _slurpvars for p in pas]
        sum(inds) == 0 && return  PatternMatch(false, Dict())
        sum(inds) > 1 && throw(ArgumentError("too many slurping variables at this level"))
        # now reduce eas to match
        bas = collect(copy(eas))
        head_eas = Basic[]
        tail_eas = Basic[]
        n = length(pas)
        for i in 1:n
            if !(pas[i] in _slurpvars)
                push!(head_eas, shift!(bas))
            else
                break
            end
        end
        for i in 1:n
            if !(pas[n-i+1] in _slurpvars)
                unshift!(tail_eas, pop!(bas))
            else
                break
            end
        end
        mids = op == :Mul ? prod(bas) : sum(bas)
        eas = vcat(head_eas, mids, tail_eas)
    end

    for (e,p) in zip(eas, pas)
        if p in _slurpvars
            matches[p] = e
        elseif !(p in _allvars)
            out = pattern_match(e, p, matches)
            if out.match == false
                return PatternMatch(false, Dict())
            end
        else
            if p in _vars
                if haskey(matches, p)
                    matches[p] == e || return PatternMatch(false, Dict())
                else
                    matches[p] = e
                end
            else
                matches[__] = e
            end
        end
    end
    return PatternMatch(true, matches)
end

