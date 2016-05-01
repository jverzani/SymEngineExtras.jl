

## this should be in SymEngine/src/subs.jl

function Base.call(ex::Basic, args...)
    xs = free_symbols(ex)
    subs(ex, collect(zip(xs, args))...)
end


## function (ex::Basic)(args...)
##     xs = SymEngine.free_symbols(ex)
##     subs(ex, collect(zip(xs, args))...)
## end
