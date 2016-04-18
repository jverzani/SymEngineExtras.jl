using SymEngineExtras, SymEngine
using Base.Test

x,y,z = symbols("x y z")

## logsimp
@test logsimp( 2log(x)) == log(x^2)
@test logsimp(log(x) + log(y)) == log(x*y)
@test logsimp(log(x) - log(y)) == log(x/y)
@test logsimp(log(x) + log(2x) - log(y) + x) == x + log(2*x^2/y)
@test logsimp(3 * log(x)) == log(x^3)
@test logsimp(y * log(x)) == log(x^y)

## expand_log
@test expand_log(log(x*y)) == log(x) + log(y)
@test expand_log(log(x/y)) == log(x) - log(y)
@test expand_log(x + log(2*x^2)) == x + log(Basic(2)) + 2*log(x)
@test expand_log(log(x^3)) == 3 * log(x)
@test expand_log(log(x^y)) == y * log(x)

## powsimp
@test powsimp(x^2 * x^3) == x^5
@test powsimp(x^2 * x^y) == x^(2+y)
@test powsimp(x + log(x^2 * x^y)) == x + log(x^(2 + y))
@test powsimp(x^2*y^2*2) == 2*(x*y)^2
@test powsimp(x^3 * y^3) == (x*y)^3 # broken, as it gets put together, taken apart

## powdenest
@test powdenest(2^(3*x)) == 8^x


## expand_power_exp
@test expand_power_exp(x^(y+z)) == x^y * x^z


## expand_power_base
@test expand_power_base((x*y)^z) == x^z * y^z


## rewrite_trig
@test rewrite_trig(sec(x)) == 1/cos(x)
@test rewrite_trig(sech(x)) == 1/cosh(x)
@test rewrite_trig(cos(cot(x))) == cos(1/tan(x))

## expand_trig
@test expand_trig(sin(x + y)) == sin(x)*cos(y) + sin(y) * cos(x)
@test expand_trig(sin(2x)) == 2*sin(x) * cos(x)
@test expand_trig(sin(x/2)^2) == (1-cos(x))/2

@test expand_trig(cos(x + y)) == cos(x)*cos(y) - sin(y) * sin(x)
@test expand_trig(x*y + cos(x + y)) == x*y + cos(x)*cos(y) - sin(y) * sin(x)
@test expand_trig(cos(2x)) == cos(x)^2 - sin(x)^2
@test expand_trig(cos(x/2)^2) == (1+cos(x))/2

@test expand_trig(tan(x + y)) == (tan(x) + tan(y)) / (1 - tan(x)*tan(y))
@test expand_trig(tan(2x)) == 2*tan(x) / (1 - tan(x)^2)
@test expand_trig(tan(x/2)) == sin(x) / (1 + cos(x))

@test expand_trig(sinh(x + y)) == sinh(x)*cosh(y) + sinh(y) * cosh(x)
@test expand_trig(sinh(2x)) == 2 * sinh(x) * cosh(x)
@test expand_trig(sinh(x/2)^2) == (cosh(x) - 1)/2


## trigsimp
@test trigsimp(2*sin(x)*cos(x)) == sin(2x)
@test trigsimp(2*sin(sin(x))*cos(sin(x)) * cos(x) * sin(x) * tan(x)) == (1//2)*sin(2*x)*sin(2*sin(x))*tan(x)
ex = sin(sin(sin(2x)))
@test trigsimp(expand_trig(ex)) == ex

@test trigsimp(2*sinh(exp(x))*cosh(exp(x))) == sinh(2exp(x))

ex = sin(x)*cos(y) + sin(y)*cos(x)
@test trigsimp(ex) == sin(x + y)


ex = sin(x)*cos(y) - sin(y)*cos(x)
@test trigsimp(ex) == sin(x - y)


ex = sin(x)*cos(y) + cos(x)*sin(y)
@test trigsimp(ex) == sin(x + y)


ex = cos(x)*cos(y) - sin(x)*sin(y)
@test trigsimp(ex) == cos(x + y)


ex = cos(x)*cos(y) + sin(x)*sin(y)
@test trigsimp(ex) == cos(x - y)

ex = sin(cos(x) + cos(y))
@test trigsimp(expand_trig(ex)) == ex

