using SymEngineExtras, SymEngine
using Base.Test

x,y,z = symbols("x y z")

pattern_match = SymEngineExtras.pattern_match
out = pattern_match(2*sin(x), sin(_1))
@test !out.match

out = pattern_match(2*sin(x), _2 * sin(_1))
@test out.match && out.matches == Dict(_1 => x, _2 => 2)


out = pattern_match(2 + sin(x), sin(_1))
@test !out.match

out = pattern_match(2 + sin(x), _2 + sin(_1))
@test out.match && out.matches == Dict(_1 => x, _2 => 2)


out = pattern_match(sin(x), sin(_1))
@test out.match && out.matches == Dict(_1 => x)


out = pattern_match(cos(x)*sin(x), __*sin(_1))
@test out.match && out.matches == Dict(__=>cos(x), _1 => x)


out = pattern_match(x^y, _1^_2)
@test out.match && out.matches == Dict(_1=>x, _2 => y)


out = pattern_match(sin(2x)*cos(x), sin(2*_1)*___)
@test out.match && out.matches == Dict(_1=>x, ___ => cos(x))

## slurp..
out = pattern_match(sin(x) + cos(x) + x + sin(y), sin(_1) + cos(_1) + __1)
@test out.match && out.matches == Dict(_1=>x, __1 => x + sin(y))


out = pattern_match(-sin(x), _2*sin(_1))
@test out.match && out.matches == Dict(_1=>x, _2 => -1)

out = pattern_match(-sin(x)*cos(y), sin(_1)*cos(_2))
@test !out.match 

out = pattern_match(-sin(x)*cos(y), sin(_1)*cos(_2)*_3)
@test out.match && out.matches == Dict(_1=>x, _2 => y, _3=>-1)


## multiple slurp
out = pattern_match(sin(x) + x + sin(x + cos(x) + tan(x) + x^2), __1 + sin(_1 + __2))
@test out.match && out.matches == Dict(__1=>x + sin(x),_1=>cos(x),__2=>x + x^2 + tan(x))

x,y,z,a,b,c = symbols("x y z a b c")
## ismatch
@test ismatch(_1, sin(x))              == true
@test ismatch(_1^_2, x^y)              == true
@test   match(_1^_1, x^y).match        == false
@test ismatch(_1^_1, x^y)              == false
@test   match(sin(_1), x^sin(x)).match == false
@test ismatch(sin(_1), x^sin(x))       == true

## cases
cs = cases([x^2, x^3, sin(x)], x^_1)
is = [c[2] for c in cs]
@test is == [1,2]

## find
@test find(x + x^2 + x^3, x)           == Set(Any[x])
@test find(x + x^2 + x^3, x^_1)        == Set(Any[x^3,x^2])
@test find(expand((sin(x)+sin(y))*(a+b)), sin(_1)) == Set(Any[sin(x),sin(y)])

## replaceall
@test replaceall(sin(x), sin(_1) => sin(y)) == sin(y)
@test replaceall(a^2+b^2+(x+y)^2 +c, _1^2=>_1^3) == a^3 + b^3 + (x + y)^3 + c
