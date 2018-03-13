##################################################
##
## Pattern matching. Follows the easier part of the masters
## thesis referenced here
## https://github.com/HPAC/matchpy/blob/master/matchpy/
##
## Part of the code in `pm.jl` is derived from the MIT licensed code
## of https://github.com/HPAC/matchpy/blob/master/matchpy/
##
## 
## SymEngine things
BasicType = SymEngine.BasicType

head(ex::Basic) = SymEngine.get_symengine_class(ex)
args(ex::Basic)::Vector{Basic} = SymEngine.get_args(ex)



## call a SymEngine function from a symbol
call_fun(fn::Symbol, args) = call_fun(Val{fn}, fn, args)
call_fun(::Type{Val{:Add}}, fn, args) = isempty(args) ? Basic(0) : _call_fun(fn, args)
call_fun(::Type{Val{:Mul}}, fn, args) = isempty(args) ? Basic(1) : _call_fun(fn, args)
call_fun(::Type{Val{T}}, fn, args) where {T} = _call_fun(fn, args)
_call_fun(fn, args) = eval(Expr(:call, SymEngine.map_fn(fn, SymEngine.fn_map),args...))



#using Multisets
_setdiff(m1::Multiset, m2::Multiset) = m1 - intersect(m1, m2)

### Utilities ##################################################

## return vectors of vals, counts (sorted) as a tuple
tally(ps::Vector) = tally(Multiset(ps))
function tally(ps::Multiset{T}) where {T}
    d = Dict{T, Int}()
    for k in collect(ps)
        haskey(d, k) ? (d[k]+=1) : (d[k] = 1)
    end
    ks = collect(keys(d))
    vs = collect(values(d))

    sigma = sortperm(vs, rev=true)
    (ks[sigma], vs[sigma])
end

# so we can call repeat(a,m) to get what we want for a vector or not
_repeat(a::Basic;inner=times) = repeat([a], inner=inner)

### Define wildcard patterns ##############################################


# this allocates, and there isn't much to do about it
# x_: regular variable: 1 match (dot variable)
# x__: match 1 or more terms (plus variable) (in * or +)
# x___: match 0, 1 or more terms (star variable)
_check_dashes(u, pattern, ::Type{Val{false}}) =  endswith(u, pattern) ##startswith(u, pattern) || endswith(u, pattern)
function _check_dashes(u, pattern, ::Type{Val{true}})
    _check_dashes(u, pattern, Val{false}) && !_check_dashes(u, pattern*"_", Val{false})
end

iswildcard(x,exact=false) = issymbolic(x) && _check_dashes(SymEngine.toString(x), "_", Val{exact})
ispluswildcard(x, exact=false) = issymbolic(x) && _check_dashes(SymEngine.toString(x), "__", Val{exact})
isstarwildcard(x, exact=false) = issymbolic(x) && _check_dashes(SymEngine.toString(x), "___", Val{exact})

onlywildcard(x) = iswildcard(x,true)
onlypluswildcard(x) = ispluswildcard(x, true)
onlystarwildcard(x) = isstarwildcard(x, false)  ## 3 or more is star wildcard

isconstantpattern(p::Basic) = length(filter(iswildcard, free_symbols(p))) == 0
isconstantpattern(fn::Symbol) = true

## we use \phi_ for wildcards we don't care about "___" in match py
const ignore_wildcard_re = r"^ϕ"
function ignore_wildcard(x)
    issymbolic(x) || return false
    s = SymEngine.toString(x)
    _check_dashes(s, "_") || return false
    return ismatch(ignore_wildcard, s)
end

# ### Constraints XXX not implemented

# struct Constraint{S,T}
# op::S
# lhs::T
# rhs::T
# end
# function Base.show(io::IO, p::Constraint)
#     println(io, p.lhs, " ", p.op, " ", p.rhs)
# end

# ## Evaluate a constraint returning true or false using values in x, a dictionary
# (p::Constraint)(x)::Bool = p.op(p.lhs(x...), p.rhs(x...))

# # the main constraints    
# Gt(a,b)  = Constraint(>,  Basic(a),Basic(b))
# Ge(a,b)  = Constraint(>=, Basic(a),Basic(b))
# Eq(a,b)  = Constraint(==, Basic(a),Basic(b))
# Neq(a,b) = Constraint(!=, Basic(a),Basic(b))
# Le(a,b)  = Constraint(<=, Basic(a),Basic(b))
# Lt(a,b)  = Constraint(<,  Basic(a),Basic(b))


## some predicates on values
import Base: isinteger, isnumber, iseven, isodd

issymbolic(::BasicType{Val{:Symbol}}) = true
issymbolic(::BasicType) = false
issymbolic(x::Basic) = issymbolic(BasicType(x))

isnumber(::T) where {T <: SymEngine.BasicNumber} = true
isnumber(::BasicType) = false
isnumber(x::Basic) = isnumber(BasicType(x))

iseven(x::Basic) = isnumber(x) && iseven(N(x))
isodd(x::Basic) = isnumber(x) && isodd(N(x))

ispositive(x::Union{BasicType{Val{:Integer}}, BasicType{Val{:Rational}}}) = x > 0
ispositive(::BasicType) = false
ispositive(x::Basic) = ispositive(BasicType(x))


isinteger(x::BasicType{Val{:Integer}}) = true
isinteger(::BasicType) = false
isinteger(x::Basic) = isinteger(BasicType(x))



## Functions

arity(fn::Type{Val{:Symbol}}) = 0
arity(fn::T) where {T <: SymEngine.BasicNumber} = 0
arity(fn::Type{Val{:Pow}}) = 2
arity(fn::Type{Val{:Add}}) = 99
arity(fn::Type{Val{:Mul}}) = 99
arity(fn::Type{Val{T}}) where {T} = 1
arity(fn::Symbol) = arity(Val{fn})

iscommutative(::Type{Val{:Add}}) = true
iscommutative(::Type{Val{:Mul}}) = true
iscommutative(::Type{Val{T}}) where {T} = false
iscommutative(fn::Symbol) = iscommutative(Val{fn})

isassociative(::Type{Val{:Add}}) = true
isassociative(::Type{Val{:Mul}}) = true
isassociative(::Type{Val{T}}) where {T} = false
isassociative(fn::Symbol) = isassociative(Val{fn})


## Dictionary things
function compatible_substitutions(d::Dict, d1::Dict)
    for k in intersect(keys(d), keys(d1))
        d[k] == d1[k] || return false
    end
    return true
end

# filter for compatability then merge. Returns new Set, does not mutate
function checked_merge(theta::Set, sigma::Dict)
    if length(theta) >= 1
        cmpts = filter(d -> compatible_substitutions(d, sigma), theta)
        map(u->merge(sigma, u), cmpts)
    else
        Set((sigma, ))
    end
end

# what is this???
function checked_merge(theta::Set, thetap::Set)
    if length(theta) == 0
        return thetap
    end
    out = Set()
    for m in thetap
        for m1 in theta
            if compatible_substitutions(m, m1)
                push!(out, merge(m, m1))
            end
        end
    end
    out

end


## Implement matchpy things
# out type
U = Union{Basic, Vector{Basic}, Tuple{Symbol, Vector{Basic}}}
#aDict(args...) = Dict{Basic, U}(args...)
aDict(args...) = Dict{Basic, Any}(args...)
empty_set() = Set(Dict{Basic, Any}[])
    
const blank_dict = aDict()
const ↯ = (false, blank_dict)
const NO_MATCH = Set(Dict{Basic,Any}[])


## return (Bool, Dict{Basic,Basic})
## Syntactic -- not associative *or* commutative
## must match exactly
## returns a tuple `(success, sigmap)`
## A match, sigmap, extends sigma and satisfies p(sigmap...) = s
function syntactic_match(s, p, sigma=aDict())  # subject, pattern, sigma::Dict

    isconstantpattern(p) && return (p==s, blank_dict)
    
    if onlywildcard(p)
        sigmap = aDict(p=>s)
        val = compatible_substitutions(sigma, sigmap)
        return (val ? (val, merge(sigma, sigmap)) :  (val, sigma))
    end

    head(s) != head(p) && return (false,↯)

    s_args, p_args = args(s), args(p)
    length(s_args) != length(p_args) && return (false, ↯)

    for i in eachindex(s_args)
        success, sigmap = syntactic_match(s_args[i], p_args[i], sigma)

        !success && return  (false, ↯)
        !compatible_substitutions(sigmap, sigma) && return (false, ↯)

        merge!(sigma, sigmap)
    end
    return (true, sigma)
end

#
## ss an array of subjects
## p a pattern
## fa a symbol representing an *associative function*, :Add, :Mul. Use :nothing for nothing
## Theta a set of valid (partial) substitutions
## returns a sset
"""
    match_one_to_one

Match a subject with one term

Length `ss` must be 1 to match, unless`p` is a star or plus wildcard

* `ss` is a collection of subjects
* `p` a pattern
* `theta` a set of partial substitutions.
* `comm` if true, the ss values may be permuted to match
* `assoc` if true, wildcards are used like plusvariables,
* `fn` a function symbol of an associative function (e.g, `:Add` and `:Mul`.)

Returns a set extending theta.
"""
function match_one_to_one(ss, p, theta::Set=Set((aDict(),)),
                          comm=false,  fn=:nothing, assoc=fn==:nothing?false:isassociative(fn))
    
    n = length(ss)
    # p in F0
    if isconstantpattern(p) 

        n == 1 && p == ss[1] && return checked_merge(theta, aDict())  

    elseif onlywildcard(p) && !assoc        # regular variable pattern

        sigmap = Dict(p=>ss[1])
        n == 1 && return checked_merge(theta, sigmap)

    elseif iswildcard(p)        # sequence variable pattern?

        if assoc  && fn != :nothing ## associative function then we can combine
            sigmap = Dict(p=>call_fun(fn, ss))
        elseif assoc || !onlywildcard(p)
            sigmap = Dict(p=>ss)           # matches the rest e.g. a + x_ ~ a + b + c = a + (b+c), so x_ => b+c
        end

        (isstarwildcard(p) || n >= 1) && return checked_merge(theta, sigmap)


    elseif n == 1

        h = head(p)
        if h == head(ss[1])
            qas, pas = args(ss[1]), args(p)

            # really here we want to pass along only :Add and :Mul
            fap = isassociative(h) ? h : :nothing
            out = Set()
            for sigma in theta
                out = union(out, Set(match_sequence(qas, pas, sigma, Val{iscommutative(fap)}, fap)))
            end
            return out
        end
    end
    
    return NO_MATCH
    
end
##################################################

## If p is a pattern and s a subject, then a match is a
## dictionary sigma whose keys are wildcards such that
## p(sigma...) = s
## 
## This function performs a partial substitution by sigma
function _psubs(patterns, sigma::Pair{Basic, Basic})
    subs.(patterns, sigma)
end

# [x_,x__,y_] subs {x_=>1, x__=>[2,3,4], y_=>[5,6]} --> [1, 2,3,4,5,6] flattened one level
function _psubs(patterns, sigma::Pair{Basic, Vector{T}}) where {T}
    k,v = sigma
    out = Basic[]
    for s in patterns
        if k in free_symbols(s)
            append!(out, [subs(s, k=>vi) for vi in v])
        else
            push!(out, s)
        end
    end
    out
end

function psubs(patterns, sigma::Dict)
    out = patterns
    for (k,v) in sigma
        out = _psubs(out, k=>v)
    end
    out
end


## reduce after partial substitutions. Return multiset
function reduce_subjects_patterns(subjects, patterns, sigma)
    mss = Multiset(collect(subjects))  # collect so tuples work
    ps = psubs(patterns, sigma)
    mps = Multiset(collect(ps))
    mss - mps, mps - mss
end

## is there an issue with patterns.(sigma) ~ subjects
function so_far_so_good(subjects, patterns, sigma)::Bool
    lhs, rhs = collect.(reduce_subjects_patterns(subjects, patterns, sigma))
    ## we are bad if there are non constants on right (as constants are matched up)
    nconsts = length(filter(isconstantpattern, rhs))
    nconsts > 0 && return false
    length(rhs) - nconsts == 0 && length(lhs) > 0 && return false
    ## we are bad if rhs has wildcards or star
    return true
end
##

##################################################

## Helper functions
function remove_constant_patterns(subjects, patterns, sigma=Dict())
    lhs, rhs = reduce_subjects_patterns(subjects, patterns, sigma)
    collect(_setdiff(lhs, rhs)), collect(_setdiff(rhs, lhs))
end

# check that matched variables in sigma are goo
function check_matched_variables(subjects, patterns, sigma::Dict)
    if so_far_so_good(subjects, patterns, sigma)
        (sigma,)
    else
        ()
    end
end



### helpers for non-variable pattern check

function _ms(u)
    p,s,sigma = u
    hp, hs = head(p), head(s)
    hp != hs && return ()
    
    comm = Val{iscommutative(hp)}
    fn, assoc = isassociative(hp) ? (hp, true) : (:nothing, false)

    match_sequence( args(s), args(p), sigma,
                       comm, fn, assoc)
end

function _check_pp(p, ss, sigma=Dict())
    o = generator_chain((),
                        () -> (s for s in ss),
                        (s) -> _ms((p,s,sigma))
                        )

    o
end

## take expressions like `sin(x_)` and check
function check_non_variable_patterns(ss, ps, sigma)

    ss, ps = reduce_subjects_patterns(ss, ps, sigma)
    ps = collect(Iterators.filter(!iswildcard, collect(ps))) # compound expressions

    isempty(ps) && return (sigma,)
    
    theta = Set()
    op = generator_chain((sigma,),
                            ((sigma) -> _check_pp(ps[i], collect(ss), sigma) for i in eachindex(ps))...,
                            (sigma) -> sigma in theta ? () : (push!(theta, sigma); (sigma,))
                            )
    op
end

### --------------------------------------------------


## Check regular variables helper
function assign_wildcard(p, k, sks,svs, sigma)
    out = Set()
    for (i, (val, nk)) in enumerate(zip(sks, svs))
        nk < k && continue
        if haskey(sigma, p)
            sigma[p] == val || continue
        end
        svscopy = copy(svs)
        svscopy[i] -= k
        push!(out, (sks, svscopy, merge(sigma, Dict(p=>val))))
    end
    out
end

function check_regular_variables(subjects, patterns, sigma::Dict)

    ## we reduce subjects, patterns, then use our algorithm
    ss, ps = remove_constant_patterns(subjects, patterns, sigma)

    sks, svs =  tally(ss)
    pks, pvs = tally(filter(onlywildcard, ps))


    o = generator_chain((),
                        () -> ((sks, svs, sigma),),
                        (u-> assign_wildcard(p, v, u...) for (p,v) in zip(pks, pvs))...,
                        (u) -> ((u[3],))
                           )
    o
end

### --------------------------------------------------




### --------------------------------------------------

## Check for sequence variables

## return generator
function _check_sv_init(ss, ps, sigma, fn, assoc, allvars, svals, N)
    ss, ps = remove_constant_patterns(ss, ps, sigma)

    plusvs = Basic[]
    starvs = Basic[]
    for p in ps
        if onlypluswildcard(p) || (assoc && onlywildcard(p))
            push!(plusvs, p)
        elseif onlystarwildcard(p)
            push!(starvs, p)
        end
    end
    
    nplus = length(plusvs)
    if nplus > length(ss)
        return empty_set() # too many plus variables
    end

    
    nstars = length(starvs)
    _svals, scnts = tally(ss)
    plusvals, pluscnts = tally(plusvs)
    starvals, starcnts = tally(starvs)

    
    theta = empty_set()

    empty!(allvars)
    append!(allvars,vcat(plusvals, starvals))
    empty!(svals)
    append!(svals, _svals)
    empty!(N)
    push!(N, length(plusvals))
    
    ## nothing to do
    if isempty(allvars) # nothing to do
        if length(ss) > 0
            return empty_set() # can't eat up ss values
        else
            return Set((sigma,))
        end
    end

    if length(plusvals) > length(ss)
        return Set()
    end
    if length(ss) == 0
        sigmap = Dict(k=>(fn==:nothing ? Basic[] : call_fun(fn, Basic[])) for k in starvals)
        out = empty_set()
        if compatible_substitutions(sigma, sigmap)
            push!(out, merge(sigma, sigmap))
        end
        return out
    end

    
    cfs = vcat(pluscnts, starcnts)

    gens = (solve_linear_diophantine(cnt, cfs) for cnt in scnts)
    itr = gen_product(gens...)

    itr
end

function _allocate_sols(sols, sigma, fn, allvars, svals, N)
    
    d = aDict()
    star_ok = true

    for (i,var) in enumerate(allvars)
        this_many = [a[i] for a in sols]
        if i <= N[1] && sum(this_many) == 0
            star_ok=false
            break
        end
        val = Basic[]
        for k in eachindex(this_many)
            nvals = _repeat(svals[k], inner=this_many[k])
            append!(val, nvals)
        end

        # wrap in associative function
        d[var] = isassociative(fn) ? call_fun(fn, val) : val

    end

    !star_ok && return ()
    if compatible_substitutions(sigma, d)
        sigmap = merge(sigma, d)
        return (sigmap,)
    end
    return ()
end

### When matching [a,a,a,a,b,b,c] ~ [x__, x__, y___] we need to
## solve equations 4 = 2x + y where 4 is number of a's, x >=1 and y >= 0
## this has solutions (2,0), (1,2), and (0,4)
## 2 = 2x + y: (1,0), (0,2)
## 1 = 2x + y: (0,1)
## we then combine (2,0),(1,0), and (0,1) -> x__ -> [a,a,b], y__ -> [c]
## (2,0),(0,2),(0,1) -> x__ -> [a,a], y___ -> [b,b,c] ...
## sigma -> generator of sigmas...
##
## The code copies some of that in matchpy for solving linear diophantine equations
function check_sequence_variables(ss, ps, sigma,
                                  fn=:nothing, assoc=false)
    
    allvars= Basic[]  # not so pretty as we want to share values across chain
    svals = Basic[]
    N = Int[]

    o = generator_chain((),
                        () -> _check_sv_init(ss, ps, sigma, fn, assoc, allvars, svals, N),
                        (sols) -> _allocate_sols(sols, sigma, fn, allvars, svals, N))

    o
end

### --------------------------------------------------

## Assemble pieces for matching ss ~ ps with commutative or associative

abstract type AbstractMatchObject end
function Base.show(io::IO, o::AbstractMatchObject)
    if isempty(o)
        println(io, "Empty match object")
    else
        println(io, "Non-empty, iterable match object. Use `first` to see one, `collect` for all.")
    end
end


## iterator interface for MatchObjects
## These just make the interace nicer
struct MatchObject <: AbstractMatchObject
itr
end
Base.iteratorsize(itertype::MatchObject)= Base.SizeUnknown()
Base.start(o::MatchObject) = start(o.itr)

Base.done(o::MatchObject, st) = done(o.itr, st)
Base.next(o::MatchObject, st) = next(o.itr, st)

###  --------------------------------------------------

# allocate fixed sum values
function allocate_ks_to_vars(ks, ss, ps, sigma, fn, assoc)
    i,j=0,0 #1,1
    thetap = Set((deepcopy(sigma),))
        
    for pl in ps
        lsub = 1 
        if ispluswildcard(pl) || (iswildcard(pl) && assoc)
            lsub = lsub + ks[1+j]
            if onlystarwildcard(pl)
                lsub -= 1
            end
            j += 1
        end
        ssp = ss[(i+1):(i+lsub)]
        fn, assoc = isassociative(fn) ? (fn, true) : (:nothing, assoc)

        thetap = match_one_to_one(ssp, pl, thetap, Val{false}, fn, assoc)
        if isempty(thetap)
            break
        end
        i += lsub 
    end

    thetap
end


## non-commutative matching
function match_sequence(ss, ps, sigma, commutative::Type{Val{false}},
                        fn=:nothing, assoc=fn==:nothing?false:isassociative(fn))

    n, m = length(ss), length(ps)
    
    ## number of star variables (zero, onem or more). Here
    ## m - nstar number of patterns that must match, if more than n too many
    nstar, nplus = 0, 0
    for p in ps
        onlystarwildcard(p) && (nstar += 1)
        (onlypluswildcard(p) || (assoc && onlywildcard(p))) && (nplus += 1)
    end
    m - nstar > n && (return empty_set())  # XXX the plus vars must match
    nfree = n - m + nstar
    nseq = nstar + nplus        #  number of sequence variables

    if nseq == 0 && nfree > 0
        return empty_set()   # generator of substitutions
    end



    itr = generator_chain((),
                             () -> fixed_sum(nseq, nfree),
                             (ks) -> allocate_ks_to_vars(ks, ss, ps, sigma, fn, assoc))



    MatchObject(itr)
end

###  --------------------------------------------------

# commutative matching
function match_sequence(ss, ps, sigma::Dict,
                        commutative::Type{Val{true}},
                        fn=:nothing,  assoc=fn==:missing?false:isassociative(fn))

    ss, ps = remove_constant_patterns(ss, ps)
    for p in ps
        isconstantpattern(p) && return NO_MATCH
    end
    length(ps) == 0 && length(ss) > 0 && return NO_MATCH

    theta = Set((sigma,))

    if length(ps) == 0
        theta = checked_merge(theta, Set((aDict(),)))
        return theta
    end

    
    itr = generator_chain((),
                          () -> theta,
                          sigma -> check_matched_variables(ss, ps, sigma),                                                           sigma -> check_non_variable_patterns(ss, ps, sigma),
                          sigma -> check_matched_variables(ss, ps, sigma),
                          sigma -> assoc ? ((sigma,)) : check_regular_variables(ss, ps, sigma),
                          sigma -> check_sequence_variables(ss, ps, sigma, fn, assoc)
    )

    MatchObject(itr)
end
 
    


##################################################

## Matching API
export matches

"""

    match(p::Basic, s::Basic, sigma)

Match subject `s` against pattern `p`.

This is syntactic matching.

An expression can be broken down into an abstract syntax tree.

For example
* `sin(x^2+1)`  has head `:Sin` and arguments `x^2+1`
* `x^2 + 1` has head `:Add` and arguments `x^2` and `1`. These arguments are ordered,
though how is not described here.
* `x^2` has head `:Pow` and arguments `x` and `2`
* `1` is a numeric value with no head and no arguments.

The expression `sin(x_)` would match `sin(x^2 + 1)` by matching `x_=>x^2 + 1`. Whereas
`x_^2` would match `x^2` with `x_=>x`. But `2^x_` would not match `x^2` as 2 does not match `x`.
The expression `x_^2 + 1` **might** match `x^2 + 1` -- but it *might* not. Why? `:Add` is commutative, but syntactic matching does not take that into account. Use `matches` for such considerations.



In a picture, the tree would look like
```
       sin(x^2 + 1)
             |
       (:Sin, x^2 + 1)
                  |
           (:Add, x^2, 1)
                  /    |
          (:Pow, x, 2)
                /    |
```
The expression `sin(x_)` matches ``(:Sin, x^2+1)`, so `x_ => x^2 + 1`

The expression `sin(x_ + 1)` *might* match `x_ => x^2` but might not. It depends on ordering, as this matching does not take into account associativity (how `1+x_` would match `1 + a + b` through `1 + (a+b)`) or commutivity.
    
Returns `(success, sigmap)`. If `!success`, `sigmap` may contain nonsense.
"""    
function Base.match(p::Basic, s::Basic, sigma=aDict())
    syntactic_match(s, p, sigma)
end


"""
    matches(patterns, subjects, sigma=Dict(); commutative=false, associative=false)

Match a list of pattern terms agains a list of subject terms.

If `commutative=true` all permutations of subjects are considered.

If `associative=true` wildcards are treated as plus wildcards. (so `x_ + y_ ~ 1 + 2 + 3`)

Patterns have "wildcards" defined through a naming convention:

* variables with one trailing slash, e.g. `x_`, are regular wildcards. They will match one term in the syntax tree unless there is an associative element, in which case they are treated as "plus" wildcards.

* variables with two trailing slashes, e.g. `x__`, are plus wildcards. They will match one or more terms.

* variables with three trailing slashes, e.g., `x___`, are star wildcards. They will match zero, one or more terms.


A value `sigma` may be specified ahead of time. This means that any
match will agree with `sigma` and satisfy `subs.(patterns, sigma...) ~
subjects`. The default is no specification
    

The return value is a generator for all valid substitutions:

* use `isempty` to check if there are any matches extending sigma.

* use `first` to get a match, when present. This mutates the generator.

* use `collect` to get all matches. This mutates the generator.

Note: Operations which return a value (or more) mutate the generator. One
must use `deepcopy` to make a copy should such behaviour be unwelcome.

Examples:

```julia

using SymEngine, SymEngineExtras
@vars a b c x_ x__ x___ y_ y__ y___

o = matches([x_, y__], [a,b,c]) # associative=false,commutative=false are defaults
first(o)                        # `x_=>a, y__=>[b,c]`
o = matches([x_, y__], [a,b,c], associative=true)
collect(o)                      # `x_=>a, y__=>[b,c]` AND `x_=>[a,b], y__=>[c]`
o = matches([x_, y__], [a,b,c], commutative=true)
collect(o)                      # `x_=>a, y__=>[b,c]` AND `x_=>b, y__=>[a,c]` AND `x_=>c, y__=>[a,b]`
                                # That is, `x_` can match ₃C₁ diferent terms
o = matches([x_, y__], [a,b,c], commutative=true, associative=true)
collect(o)                      # 6 matches, as x_ can match ₃C₁ + ₃C₂ terms now

o = matches([x__, y__], [a,b,c])
collect(o)                      # 2 matches, x__=>[a],  x__=>[a,b] (with y__ absorbing the rest)
o = matches([x__, y__], [a,b,c], commutative=true)
collect(o)                      # 6 matches as x__ can match ₃C₁ + ₃C₂ terms

o = matches([x___, y_], [a,b,c])
collect(o)                      # 1 match, as `y_=>[c]`
o = matches([x___, y__], [a,b,c])
collect(o)                      # 3 matches: ₃C₁ matches, as `x___` matches  `x___=>[], x___=>[a]`, and `x___=>[a,b]`
o = matches([x___, y__], [a,b,c], commutative=true)
collect(o)                      # 7 = ₃C₀ + ₃C₁ + ₃C₂ matches for `x___`, as y__ must have 1 match
```
"""
function matches(ps, ss, sigma=aDict(); commutative=false, associative=false)
    out = match_sequence(ss, ps, sigma, Val{commutative}, :nothing, associative)
end


"""
    matches(pattern, subject, sigma=Dict())

Matches subject against the pattern.


"""    
function matches(pattern::Basic, subject::Basic, sigma=aDict())
    # depends on head
    sh, ph = head.((subject,pattern))

    if sh == ph && arity(sh) != 0

        match_sequence(args(subject), args(pattern), sigma,
                          Val{iscommutative(sh)},
                          sh, isassociative(sh))
    else
        ## when is it okay that p ~ s but of different heads?
        ## e.g x_ + y___ ~ a with {x_=>a, y___=>[]} --> {x=>a, y=>0}
        if isassociative(ph) && arity(sh) > 0 # Add or Mul
            match_sequence([subject], args(pattern), aDict(),
                           Val{iscommutative(ph)},
                           ph, isassociative(ph))
        else
            matches([pattern], [subject], sigma)
        end
    end
end
    
## Add in guards?

## Case - not needed
# cases(ss, p) = filter(s -> !isempty(matches(x_^2, s)), [a,a^2,b^2])

## Replace all

mutable struct SyntaxTreeNode
fn::Symbol
ex::Basic
children::Vector
end

function expression_tree(ex::Basic)
    fn = head(ex)

    if fn in [:Symbol, :Integer]
        return SyntaxTreeNode(fn, ex,  SyntaxTreeNode[]) # use no children for terminal
    else
        exs = args(ex)
        children = expression_tree.(args(ex)) #[expression_tree(u) for u in exs]
        SyntaxTreeNode(fn, ex, children)
    end
end

function node_to_ex(n::SyntaxTreeNode)
    if isempty(n.children)
        n.ex
    else
        call_fun(n.fn, node_to_ex.(n.children))
    end
end

## rewrite :Sin -> :Cos, no arity check... so :Add -> :Sin is an issue

## replace function heads
function _replace(n::SyntaxTreeNode, f::Symbol, g::Symbol, traverse=true)
    if n.fn == f
        n.fn = g
    end
    if traverse
        !isempty(n.children) && _replace.(n.children, f, g, traverse)
    end
end


## replace function head with functino call
function _replace(n::SyntaxTreeNode, f::Symbol, g, traverse=true)
    if traverse && !isempty(n.children)
        _replace.(n.children, f, g, traverse)
    end
    
    if n.fn == f
        xs = node_to_ex.(n.children)
        n.ex = g(xs...)
        n.fn = :Symbol
        empty!(n.children)
    end
end


## replace call f on expression. If true, replace with g(args)
function _replace(n::SyntaxTreeNode, f, g, traverse=true)
    if traverse && !isempty(n.children)
        _replace.(n.children, f, g, traverse)
    end

    
    val = f(n.ex)
    if val
        n.ex = g(n.ex)
        n.fn = :Symbol
        empty!(n.children)
    end
end

## replace expressions
function _replace(n::SyntaxTreeNode, pattern::Basic, rpattern::Basic, traverse=true)
    
    if traverse && !isempty(n.children)
        _replace.(n.children, pattern, rpattern, traverse)
    end

    ex = node_to_ex(n)
    m = matches(pattern, ex)
    val = isempty(m)

    if !val
        sigma = first(m)
        n.ex = subs(ex, subs(pattern, sigma...), subs(rpattern, sigma...))
        # now trick node
        n.fn = :Symbol
        empty!(n.children)
    end

end

## replace
import Base: replace
"""

    replace(ex::Basic, pattern, rpattern, traverse=true)

Replace parts o expression `ex` using a pattern and a replacement
pattern. If `traverse=true`, then descend syntax tree for
replacements. Otherwise, only the top-level is considered.

The replacement dependson the type of pattern/rppattern:
    
* `pattern::Basic, rpattern::Basic`

    The pattern with wildcards is matched agains the (sub) expressions of `ex`. When there is a match, the *first* substitution found is used to substitute in the (sub) expression using this match.
    
* `pattern::Symbol, rpattern::Symbol`

    The symbols represent function heads. For example, `sin(x)` has head `:Sin`. The syntax tree is looked at and each occurrence of thefunction head `f` is replaced by the function head `g`.
        
* `pattern::Symbol, rpattern::function`

    The symbol represents a function head. For example, `sin(x)` has head `:Sin`. The syntax tree is looked at and each occurrence of the function head `f` is replaced by the function `g(args...)`.

* `pattern::function, rpattern::function`

        Each subexpression `ex` is tested by the `pattern` function. If true, the expression is replaced by `g(ex)`.

"""
function replace(ex::Basic, pattern, rpattern, traverse=true)
    n = expression_tree(ex)
    _replace(n, pattern, rpattern, traverse)
    node_to_ex(n)
end

replace(ex::Basic, pr::Pair, traverse=true) = replace(ex, pr..., traverse)
