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
        return
#    n > tot && return ()
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

        !iszero(rem(c,d)) && return NO_SOL

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
    NO_SOL
end

## solve x1*a + x2*b + ... = c for non-negative solutions
@resumable function solve_linear_diophantine(c, xs)
    NO_SOL = nothing

    n = length(xs)
    n == 0 && return NO_SOL
    if n == 1
        d,r = divrem(c, xs[1])
        r == 0 && @yield (d,)
        return NO_SOL
    end
    if n == 2
        u = base_solution_linear(xs[1], xs[2], c)
        for v in u
            @yield v
        end
        return NO_SOL
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
end


function generator_chain(init, fs...)
    GeneratorChain(fs, init, Any[], Any[], Any[])
end

Base.iteratorsize(itertype::GeneratorChain) = Base.SizeUnknown()
function Base.start(o::GeneratorChain)

    g1 = o.fs[1](o.init...)
    st =start(g1)

    empty!(o.gs)
    empty!(o.sts)
    empty!(o.vals)
    push!(o.gs, g1)
    push!(o.sts, st)
    st
end

# advance to next tip
function Base.done(o::GeneratorChain, st)
    # is vals empty? If not, pop!
    !isempty(o.vals) && return false

    # okay, work back down
    while done(o.gs[end], o.sts[end])
        pop!(o.gs)
        pop!(o.sts)
        isempty(o.gs) && return true
    end

    # now back up
    i, n = length(o.gs), length(o.fs)

    val, o.sts[end] = next(o.gs[end], o.sts[end])
    for fn in o.fs[(i+1):n]
        gi = fn(val)
        st = start(gi)
        done(gi, st) && return done(o, st)
        val, st = next(gi, st)
        push!(o.gs, gi)
        push!(o.sts, st)
    end

    push!(o.vals, val)
    return false
end

function Base.next(o::GeneratorChain, st)
    pop!(o.vals), st
end

