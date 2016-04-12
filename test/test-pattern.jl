using SymEngineExtras, SymEngine
using Base.Test

x,y,z = symbols("x y z")


out = pattern_match(sin(x), sin(_1))
@test out.match && out.matches == Dict(_1 => x)


out = pattern_match(cos(x)*sin(x), __*sin(_1))
@test out.match && out.matches == Dict(__=>cos(x), _1 => x)


out = pattern_match(x^y, _1^_2)
@test out.match && out.matches == Dict(_1=>x, _2 => y)


out = pattern_match(sin(2x)*cos(x), sin(2*_1)*__)
@test out.match && out.matches == Dict(_1=>x, __ => cos(x))

## slurp..
out = pattern_match(sin(x) + cos(x) + x + sin(y), sin(_1) + cos(_1) + ___)
@test out.match && out.matches == Dict(_1=>x, ___ => x + sin(y))
