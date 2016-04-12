## add plotting commands
##
## Based on Plots.jl v"0.5.5".  In particular, this assume Julia v"0.4"
##
##
## Our goal here is to give plotting a Julia interface
## that doesn't depend on the backend plotting packages, so we
## use the `Plots` package.
##
##
## plot(::SymbolicType, a, b)          2d-line plot of function
## plot(Vector{SymbolicType}, a, b)    plot of expressions over same axis
## plot(::SymbolicType, ::SymbolicType, a, b)   parametric plot of two expressions over [a,b]
## plot(xs, ys, ex::SymbolicType)      contour plot of expression over regions xs x ys
##
## To this we add a light interface for explicitness:
##
## parametricplot(ex1, ex2, [ex3], a, b) # parametric plot in 2 or 3d
## contourplot(ex, (xvar, a, b), (yvar, c,d))  # also Plots.contour(xs, ys, ex)
## plot_surface(ex, (xvar, a, b), (yvar, c,d)) # also Plots.surface(xs, ys, ex)
##
## we also add
## vectorfieldplot([ex1, ex2], (xvar, a, b), (yvar, a, b)) for a vector field plot
##





import Plots
import Plots: plot, plot!, Surface
export plot, plot!


################################################## Plots...
### Plug into Plots interface. Where there is something defined for Functions we
### define for symbolic expressions
function Plots._apply_recipe(d::Plots.KW, v1, v2, f::Basic, args...; kw...)
    (v1, v2, lambdify(f))
end

function Plots._apply_recipe(d::Plots.KW, s::Basic, args...; kw...)
    (lambdify(s), args...)
end
function Plots._apply_recipe(d::Plots.KW, v::AbstractVector{Basic}, args...; kw...)
    (map(lambdify, v), args...)
end

function Plots._apply_recipe(d::Plots.KW, mf1::Basic, mf2::Basic, args...; kw...)
    (lambdify(mf1), lambdify(mf2), args...)
end

function Plots._apply_recipe(d::Plots.KW, mf1::Basic, mf2::Basic, mf3::Basic, args...; kw...)
    (lambdify(mf1), lambdify(mf2), lambdify(mf3), args...)
end




##################################################
## helper function

## evaluate vals for object
function mapsubs(ex::SymbolicType, x::SymbolicType, vals::AbstractVector)
    out = Float64[]
    out = map(lambdify(ex), vals)
    map(Float64, out)
end

## This is similar to the above, but is used for two variables. It
## mimics Float64[ex(x,y) for x in xs, y in ys]
function mapsubs2(ex::SymbolicType, x,xs, y, ys)
    out = Float64[]
    fn = SymEngine._lambdify(ex, [x,y])
    out = [fn(u,v) for u in xs, v in ys]
    map(Float64, out)
end



## prepare parametic takes exs, [t0,t1] and returns [xs, ys] or [xs, ys, zs]
function _prepare_parametric(exs, t0, t1, n=250)
    vars = free_symbols(exs)
    nexs = length(exs)
    (nexs==2) | (nexs==3) || throw(DimensionMismatch("parametric plot requires the initial tuple to have 2 or 3 variables"))
    length(vars) == 1 ||  error("parametric plot allows only one free variable")

    ts = linspace(t0, t1, n)
    [Float64[convert(Float64, convert(Function, exs[i])(t)) for t in ts] for i in 1:nexs] # [[xs...], [ys...], [zs...]]
end

## parse (ex, ([x], a, b), ([y], c,d)) into variables x,y and ranges xs, ys.
function _find_us_vs(ex, xvar, yvar, n=100)
    vars = free_symbols(ex)
    if length(xvar) == 2
        U = vars[1]
        x1,x2 = xvar
    else
        U, x1, x2 = xvar
    end
    if length(yvar) == 2
        V = vars[2]
        y1,y2 = yvar
    else
        V, y1, y2 = yvar
    end
    xs = linspace(x1, x2, n)
    ys = linspace(y1, y2, n)
    U, V, xs, ys
end




##################################################



"""

Plotting of symbolic objects.

The `Plots` package provide a uniform interface to many of `Julia`'s
plotting packages. `SymEngine` extends the methods for functions to plot
symbolic objects.

The basic goal is that when `Plots` provides an interface for function
objects, this package extends the interface to symbolic
expressions.

If no backend plotting package is loaded directly, then the `plot` and
`plot!` methods of `Plots` allow for direct plotting of `SymEngine`
objects.

In particular:


* `plot(ex::SymbolicType, a, b; kwargs...)` will plot a function evaluating `ex` over [a,b]

Example. Here we use the default backend for `Plots` to make a plot:

```
@vars x
plot(x^2 - 2x, 0, 4)
```

The backend could be switched out with a call like, `pyplot()` or `backend(:pyplot)`, say.

* `plot(exs::Vector{SymbolicType}, a, b; kwargs...)` will plot the functions evaluating `exs` over [a,b]

Example:

```
@vars x
plot([sin(x), cos(x)], 0, 2pi)
```

* `plot(ex1, ex2, a, b; kwargs...)` will plot the two expressions in a parametric plot over the interval `[a,b]`.   

Example:

```
@vars x
plot(sin(2x), cos(3x), 0, 4pi) ## also 
```

For explicitness, we provide `parametricplot(ex1, ex2, a, b)` as an alternative.

For a few backends (those that support `:path3d`) a third symbolic
expression may be added to have a 3d parametric plot rendered:

```
parametricplot(sin(x), cos(x), x, 0, 4pi) # helix in 3d
```

* `vectorfieldplot([ex1, ex2], (x,x0,x1), (y,y0,y1), ...)` will create a vectorfield plot where for a grid of values `(x,y)`, a vector in the direction `[ex1, ex2]`, evaluated at `(x,y)`, will be plotted.

```
vectorfield([-y,x], (x, -5,5), (y, -5,5))
```


* `plot(xs, ys, expression)` will make a contour plot (for many backends).

```
@vars x y
plot(linspace(0,5), linspace(0,5), x*y)
```

For explicitness, we provide `contourplot(ex::SymbolicType, (xvar, a, b), (yvar, c, d))` as an alternative:

```
contourplot(x^2 - y^2, (x,-5,5), (y,-5,5)) # default is [-5,5] x [-5,5]
```



* To plot the surface  `z=ex(x,y)` over a region we have `plot_surface(ex, (x,-5,5), (y,-5,5); kwargs...)`. For example,

```
@vars x y
plot_surface(25 - (x^2 + y^2), (x,0,5), (y,0,5)) # default region could have been dropped
```

The `Plots.surface` function (for a few backends) can also make sureface plots through the syntax:

`Plots.surface(xs, ys, expression)`


* `plot_parametric_surface(exs::Tuple, (uvar,a0,b0), (vvar,a1,b1);
  kwargs)` will make parametrically defined surface plots.

Plot the parametrically defined surface `[exs[1](u,v), exs[2](u,v), exs[3](u,v)]` over `[a0,a1] x
[b0,b1]`. The specification of the variables uses a tuple of the form
`(Sym, Real, Real)` following the style of SymPy in `integrate`, say,
where disambiguation of variable names is needed.

Requires `PyPlot`.

```
@vars theta, phi
r = 1
plot_parametric_surface((r*sin(theta)*sin(phi), r*sin(theta)*cos(phi), r*cos(theta)),
                        (theta, 0, pi), (phi, 0, pi/2))
```

(The SymPy name for this function is `plot3d_parametric_surface`, we have dropped the "`3d`" part.)

"""
symengine_plotting = nothing
export symengine_plotting

## Our alternatives
"""

Create a parametric plot of the expressions over the interval `[a,b]`.

(A more explicit call of the type `plot(ex1, ex2, a, b)`.
"""
function parametricplot(ex1::SymbolicType, ex2::SymbolicType, a::Real, b::Real, args...; kwargs...)
    _parametricplot(Plots.plot, ex1,ex2,a,b, args...; kwargs...)
end
function parametricplot!(ex1::SymbolicType, ex2::SymbolicType, a::Real, b::Real, args...; kwargs...)
    _parametricplot(Plots.plot!, ex1,ex2,a,b, args...; kwargs...)
end
function _parametricplot(fn, ex1::SymbolicType, ex2::SymbolicType, a::Real, b::Real, args...; kwargs...)
    fn(ex1, ex2, a,b, args...; kwargs...)
end

function parametricplot(ex1::SymbolicType, ex2::SymbolicType, ex3::SymbolicType, a::Real, b::Real, args...; n=250, kwargs...)
    _parametricplot(Plots.path3d, ex1, ex2, ex3, a, b, args...; n=n, kwargs...)
end
function parametricplot!(ex1::SymbolicType, ex2::SymbolicType, ex3::SymbolicType, a::Real, b::Real, args...; n=250, kwargs...)
    _parametricplot(Plots.path3d!, ex1, ex2, ex3, a, b, args...; n=n, kwargs...)
end
function _parametricplot(fn, ex1::SymbolicType, ex2::SymbolicType, ex3::SymbolicType, a::Real, b::Real, args...; n=250, kwargs...)
    ts = linspace(a, b,n)
    x = free_symbols([ex1, ex2, ex2])[1]
    xs, ys, zs = [mapsubs(ex,x,ts) for ex in [ex1, ex2, ex3]]
    fn(xs, ys, z=zs, args...; kwargs...)
end
export(parametricplot)
export(parametricplot!)


"""

Vector plot. At each (x,y) on a grid, plot a "vector" of [fx(x,y), fy(x,y)], suitably scaled.

Example:
```
fx(x,y) = -y; fy(x,y) = x
vectorfieldplot(fx, fy)
```

We can plot a direction field of an ODE too.

```
F(y,x) = 1 - y/x   # solution to y'(x) = F(y(x),x) is C/x + x/2
fx(x,y) = 1; fy(x,y) = F(y,x)
vectorfieldplot(fx, fy, xlim=(1,5))
y(x) = 2/x + x/2
plot!(y, 1, 5, linewidth=3)
```

"""
vectorfieldplot(fx::Function, fy::Function; xlim=(-5,5), ylim=(-5,5),  n::Int=10, kwargs...) =
    _vectorfieldplot(Plots.quiver, fx, fy; xlim=xlim, ylim=ylim,n=n, kwargs...)
vectorfieldplot!(fx::Function, fy::Function; xlim=(-5,5), ylim=(-5,5),  n::Int=10, kwargs...) =
        _vectorfieldplot(Plots.quiver!, fx, fy; xlim=xlim, ylim=ylim,n=n, kwargs...)

function _vectorfieldplot(fn, fx::Function, fy::Function; xlim=(-5,5), ylim=(-5,5),  n::Int=10, kwargs...)

    x₀, x₁ = xlim
    y₀, y₁ = ylim
    Δx = (x₁ - x₀) / (n-1)
    Δy = (y₁ - y₀) / (n-1)

    xs = x₀:Δx:x₁
    ys = y₀:Δy:y₁
#    p = Plots.plot(xlim=xlim, ylim=ylim, legend=false, kwargs...)

    mx, my = 0.0, 0.0


    us = vec(broadcast((x,y) -> x, xs, ys'))
    vs = vec(broadcast((x,y) -> y, xs, ys'))
    dus = map(fx, us, vs)
    dvs = map(fy, us, vs)

    ## we want all lines to be in the box, so we scale
    mx = maximum(abs(dus))
    my = maximum(abs(dvs))
    λ = .95 *  min(Δx/mx, Δy/my)

    ## println(us)
    ## println(vs)
    ## println(λ *dus)
    ## println(λ *dvs)
    
    p = fn( us, vs, quiver= (λ * dus,  λ * dvs); kwargs...)
    
#    for x in xs, y in ys
#        Plots.plot!([x, x + λ * fx(x,y)], [y, y + λ * fy(x,y)])
#    end
    
    p
end


"""

Vector field plot. At each point (x,y) on a grid, plots the vector specified by the expression.

The limits are passed in as tuples of the form `(a,b)` or `(x,a,b)`. The latter specifies the symbol. The former will assign the "`x`" symbol to be the first free symbol and the "`y`" variable the second.

Example
```
@vars x y
vectorfieldplot([-y, x], (x, -5, 5), (y, -5, 5))
```
"""
function vectorfieldplot{T<:SymbolicType}(exs::Vector{T}, xvar=(-5.0, 5.0), yvar=(-5.0, 5.0);n::Int=15,
                                          kwargs...)
    _vectorfieldplot(vectorfieldplot, exs, xvar, yvar; n=n, kwargs...)
end
function vectorfieldplot!{T<:SymbolicType}(exs::Vector{T}, xvar=(-5.0, 5.0), yvar=(-5.0, 5.0);n::Int=15,
                                          kwargs...)
    _vectorfieldplot(vectorfieldplot!, exs, xvar, yvar; n=n, kwargs...)
end

function _vectorfieldplot{T<:SymbolicType}(fn,
                                           exs::Vector{T},
            xvar=(-5.0, 5.0),
            yvar=(-5.0, 5.0);
            n::Int=15,
            kwargs...) 
            
    length(exs) == 2 || throw(DimensionMismatch("vector of symbolic objects must have length 2"))
    for ex in exs
                nvars = length(free_symbols(ex))
        nvars <= 2 || throw(DimensionMismatch("Expression has $nvars, expecting 2 for a quiver plot"))
    end
    
    ## get variables, U, V, xlim, ylim
    vars = free_symbols(exs)
    if length(xvar) == 2
        U = vars[1]
        xlim = xvar
    else
        U, xlim = xvar[1], xvar[2:3]
    end
    if length(yvar) == 2
        V, ylim = vars[2], yvar
    else
        V, ylim = yvar[1], yvar[2:3]
    end

    fx = SymEngine._lambdify(exs[1], [U,V])
    fy = SymEngine._lambdify(exs[2], [U,V])

    fn(fx, fy; xlim=xlim, ylim=ylim, n=n, kwargs...)
end
export vectorfieldplot, vectorfieldplot!


"""

Create a contour plot of the expression over the indicated region. The
region is specified as a tuple `(a,b)` or `(x,a,b)`. The former has
the associated variable inferred using the ordering of `free_symbols`.

(This is a more explicit form of interface provided by `Plot`:
`plot(xs, ys, ex::Sym)`.)

"""
function contourplot(ex::SymbolicType, xvar=(-5.0, 5.0), yvar=(-5.0, 5.0), args...;
            n::Int=50, linetype=:contour, kwargs...)
    _contourplot(Plots.plot, ex, xvar, yvar, args...; n=n, kwargs...)
end
function contourplot!(ex::SymbolicType, xvar=(-5.0, 5.0), yvar=(-5.0, 5.0), args...;
            n::Int=50, linetype=:contour, kwargs...)
    _contourplot(Plots.plot!, ex, xvar, yvar, args...; n=n, kwargs...)
end
function _contourplot(fn, ex::SymbolicType,
                      xvar=(-5.0, 5.0),
                      yvar=(-5.0, 5.0),
                      args...;
                      n::Int=50,
                      kwargs...)
    U,V,xs,ys = _find_us_vs(ex, xvar, yvar, n)
    zs = mapsubs2(ex, U, xs, V,ys)
    fn(xs, ys, zs, args...; linetype=:contour, kwargs...)
end
export(contourplot)
export(contourplot!)

## XXX Rename these?? surface?)
## surface plot. Uses surface()
"""

Make a surface plot defined by the expression of two variables. 


Example
```
plot_surface(x*y, (x,0,3), (y,0,2))
```

This is an *alternative* to the use of surface plots in Plots.
That is, the above is the same as:

```
xs = linspace(0,3, 35)
ys = linspace(0,2,35)
Plots.surface(xs, ys, x*y)
```

Eventually uses `Plots.plot(..., linetype=:surf)`, so surface plots must be defined for the backend in use.
"""
function plot_surface(ex::SymbolicType,
                      xvar=(-5.0, 5.0),
                      yvar=(-5.0, 5.0),
                      args...;
                      n::Int=35,
                      kwargs...)
    
    vars = free_symbols(ex)
    length(vars) == 2 || throw(DimensionMismatch("Expression has wrong number of variables. Expecting 2 for a surface plot"))
    
    U,V,xs,ys = _find_us_vs(ex, xvar, yvar, n)        
    zs = mapsubs2(ex, U, xs, V,ys)
    
    Plots.surface(xs, ys, z=Plots.Surface(zs), args...; kwargs...)
end
export plot_surface


## ## surface plot xvar = Tuple(SymbolicType, Real, Real)
## ##
## """

## Render a parametrically defined surface plot.

## Example:
## ```
## @vars u, v
## plot_parametric_surface((u*v,u-v,u+v), (u,0,1), (v,0,1))
## ```

## Eventually uses `Plots.plot(..., linetype=:surf)`, so surface plots must be defined for the backend in use.
## """
## function plot_parametric_surface(exs::Tuple{Sym,Sym,Sym},
##                                  xvar=(-5.0, 5.0),
##                                  yvar=(-5.0, 5.0),
##                                  args...;
##                                  n::Int=25, # really small, as otherwise this takes forever to plot
##                                  kwargs...)
    
##     vars = free_symbols(exs)
    
##     nvars = length(vars)
##     nvars == 2 || throw(DimensionMismatch("Expression has $nvars, expecting 2 for a surface plot"))
            
##     U,V,us,vs = _find_us_vs(exs, xvar, yvar, n)        
    
##     xs = mapsubs2(exs[1], U, us, V,vs)
##     ys = mapsubs2(exs[2], U, us, V,vs)
##     zs = mapsubs2(exs[3], U, us, V,vs)            

##     println(typeof(xs))
##     println(typeof(zs))
    
##     Plots.surface(xs, ys, z=Surface(zs), args...; kwargs...)
## end
## export plot_parametric_surface





