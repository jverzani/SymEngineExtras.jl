using Polynomials   # requires locally hacked copy for now....

## hacky way to see if some expression is a polynomial
function _is_poly(ex::Basic)
    try
        (length(SymEngine.free_symbols(ex)) == 1) && lambdify(ex)(variable(:x))
        true
    catch err
        false
    end
end

function _coeffs(ex::Basic, var=SymEngine.free_symbols(ex)[1])
    !_is_poly(ex) && throw(ArgumentError("symbolic expression is not a univariate polynomial"))
    n = degree(lambdify(ex)(variable(:x)))
    
    # cheesy way to get coefficients from a polynomial expression
    cs = [subs(ex, var, 0)]
    for i in 1:n
        ex = diff(ex, var)
        c = subs(ex, var, 0) / factorial(i)
        push!(cs, c)
    end
    cs
end

## what to do with constants? Here we want to keep as Basic values
function Base.convert(::Type{Poly}, ex::Basic, var=SymEngine.free_symbols(ex)[1])
    cs = _coeffs(ex, var)
    Poly(cs, var)
end
    


        
    
