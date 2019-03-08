## Iteration utilities

## some algorithms are easier to write using this neat
## package. However, for complicated usage, it proved
## to have issues with recursive usage and precompilation
using ResumableFunctions

# iterator over tuples of length n that sum to tot all non-negative
# used in non-commutative matching algorithm
@resumable function fixed_sum(n, tot, ps=())
    if n == 0
        @yield ()
        return nothing
    ## for all (k1, k2, ..., kseq) st sum(ks) = nfree
    elseif n == 1
        @yield (tot, ps...)
    else
        for i = 0:tot
            for v in collect(fixed_sum(n-1, tot-i, tuple(i, ps...)))
                @yield v
            end
        end
    end
end

# This comes from https://github.com/HPAC/matchpy/blob/master/matchpy/utils.py
# MIT licensed
# solve ax + by = c
# XXX: return (-1,-1) for nothing?
@resumable function base_solution_linear(a,b,c)

    @assert a > 0 && b > 0 && c >= 0

    NO_SOL = nothing

    d = gcd(a,b,c)
    a,b,c = div.((a,b,c), d)

    if c == 0
        @yield (0,0)
    else
        d, x0, y0 = gcdx(a, b)  # d = x0*a + y0*b

        !iszero(rem(c,d)) && return nothing

        x, y = c*x0, c*y0

        if x <= 0
            while y >= 0
                if x >= 0
                    @yield (x,y)
                end
                x += b
                y -= a
            end
        else
            while x >=0
                if y >= 0
                    @yield (x,y)
                end
                x -= b
                y += a
            end
        end
    end
#    NO_SOL
end

## solve x1*a + x2*b + ... = c for non-negative solutions
@resumable function solve_linear_diophantine(c, xs)


    NO_SOL = nothing

    n = length(xs)
    n == 0 && return nothing
    if n == 1
        d,r = divrem(c, xs[1])
        r == 0 && @yield (d,)
        return nothing
    end
    if n == 2
        u = base_solution_linear(xs[1], xs[2], c)
        for v in u
            @yield v
        end
        return nothing
    end

    d = gcd(xs...)

    # solve xs[1] * x + d * y = c
    for val in base_solution_linear(xs[1], d, c)
        nxs = div.(xs[2:end], d)
        x, y = val
        for val in solve_linear_diophantine(y, nxs)
            @yield tuple(x, val...)
        end
    end

    NO_SOL
end

# trim iterator to yield only unique values
@resumable function just_unique(itr)
    theta = Any[]
    for i in itr
        if !(i in theta)
            @yield i
            push!(theta, i)
        end
    end
end

# Product generator
# for i in g1, j in g2, k in g3 ...
# do something with (i,j,k,...)
# end
# This is Iterators.product, but that was failing or some
# resumable functions
function gen_product(gens...)
    if length(gens) == 1
        [(i,) for i in collect(gens[1])] # not just collect(gens[1])
    elseif length(gens) == 2
        [tuple(g,h) for g in collect(gens[1]), h in gens[2]]
    else
        return [tuple(g, h...) for h in gen_product(gens[2:end]...), g in collect(gens[1])]
    end
end



## Create generator to cover case of
## for i in f1()
##    for j in f2(i)
##       for k in f3(j) ...
##
## Uses a backtracking algorithm
mutable struct GeneratorChain
fs
init
gs
sts
vals
needall
end


function generator_chain(init, fs...; needall=false)
    GeneratorChain(fs, init, Any[], Any[], Any[], needall)
end

Base.IteratorSize(itertype::GeneratorChain) = Base.SizeUnknown()


# compute generator for level i
# using input from level i-1. If i-1==0, then usese init...
# finds first element of generator
# * if non empty, stores generator, state, value and return true
# * if empty, return false
function compute_gi(o, i)
    fi = o.fs[i]
    gi = i == 1 ? fi(o.init...) : fi(o.vals[i-1])

    iter_val = iterate(gi)
    isnothing(iter_val) && return false

    val, st = iter_val
    push!(o.gs, gi)
    push!(o.sts, st)
    push!(o.vals, val)

    return true
end

# Move to end
function Base.iterate(o::GeneratorChain)
    empty!(o.gs)
    empty!(o.sts)
    empty!(o.vals)
    for (i, fi) in enumerate(o.fs)
        if !compute_gi(o,i)
            o.needall && return (missing, true)
            break
        end
    end
    return (o.vals[end], true)
end

function Base.iterate(o::GeneratorChain, st)
    !st && return nothing

    ## state is kept in o
    k = length(o.sts)
    iszero(k) && return nothing
    n = length(o.fs)

    iter_val = iterate(o.gs[k], o.sts[k])
    if !isnothing(iter_val)
        ## move forward
        val, st = iter_val
        o.vals[k] = val
        o.sts[k] = st

        for i in (k+1):length(o.fs)
            if !compute_gi(o,i)
                o.needall && return (missing, true)
                break
            end
        end
        return (o.vals[end], true)
    end


    while isnothing(iter_val)
        pop!(o.gs); pop!(o.sts); pop!(o.vals)
        k = length(o.sts)
        iszero(k) && return nothing

        iter_val =  iterate(o.gs[k], o.sts[k])
    end

    # Now go forward base one
    isnothing(iter_val) && return nothing
    val, st = iter_val
    o.sts[k] = st
    o.vals[k] = val

    # now go to tip
    for i in (k+1):length(o.fs)
        if !compute_gi(o,i)
            o.needall && return (missing, true)
            break
                break
            end
    end
    return (o.vals[end], true)

end
