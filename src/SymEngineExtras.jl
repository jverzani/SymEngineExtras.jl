__precompile__(true)
module SymEngineExtras

using SymEngine
using Base.Iterators
using ResumableFunctions
using Multisets
using Combinatorics


SymbolicType = SymEngine.SymbolicType
BasicType = SymEngine.BasicType


# package code goes here
include("iterator-utils.jl")
include("patternmatch.jl")
include("simplify.jl")


end # module
