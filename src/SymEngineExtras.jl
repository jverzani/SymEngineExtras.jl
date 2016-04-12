module SymEngineExtras

using SymEngine
SymbolicType = SymEngine.SymbolicType
BasicType = SymEngine.BasicType

# package code goes here
#include("polynomials.jl")
include("plots.jl")
include("patternmatch.jl")
include("simplify.jl")

end # module
