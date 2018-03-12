

## Test
using Base.Test
using Base.Iterators
using SymEngine
using SymEngineExtras
PM = SymEngineExtras

@vars a b c x y z x_ x__ x___ y_ y__ y___ z_ z__ z___

@testset "syntactic match (non assoc, non comm)" begin
    d = Dict()
    success, d = PM.syntactic_match(a, x_, d)
    @test success
    
    d = Dict()
    success, d = PM.syntactic_match(sin(a), sin(x_), d)
    @test success
    
    d = Dict()
    success, d = PM.syntactic_match(a^b, x_^b, d)
    @test success
    
    d = Dict()
    success, d = PM.syntactic_match(b^a, b^x_, d)
    @test success
    
    d= Dict()
    success, d = PM.syntactic_match(a^a, x_^x_, d)
    @test success
    
    d= Dict()
    success, d = PM.syntactic_match(a^b, x_^x_, d)
    @test !success
    
    d= Dict(x_=>b)
    success, d = PM.syntactic_match(a^a, x_^x_, d)
    @test !success
    
end

@testset "match one to one" begin
    ## possibly assoc, poss comm helper
    Theta = Set((PM.aDict(),))
    theta = PM.match_one_to_one([a], x_, Theta)
    @test length(collect(theta)) == 1 && collect(theta)[1][x_] == a
    
    
    theta = PM.match_one_to_one([sin(a)], sin(x_), Theta)
    @test length(collect(theta)) == 1 && collect(theta)[1][x_] == a

    subject = [x, 2x, 3x]
    theta = PM.match_one_to_one(subject, x_, Theta, true, :Add)
    @test length(theta) == 1
    @test collect(theta)[1] == Dict(x_=>6x)

    theta = PM.match_one_to_one(subject, x_, Theta)
    @test length(theta) == 0

    theta = PM.match_one_to_one(subject, x__, Theta)
    @test length(theta) == 1 # x__ -> pattern

    theta = PM.match_one_to_one([x,x,x],x_, Theta)
    @test isempty(theta)

    theta = PM.match_one_to_one([x],x_, Theta)
    @test !isempty(theta)

end

@testset "match_sequence" begin
    ## poss assoc, not commutative
    sigma = Dict()
    subject = [a,b,c,a,b,c]
    pattern = [x__,y___,a,b,x_]
    theta = PM.match_sequence(subject, pattern, sigma, Val{false})
    d = Dict(x_=>c,x__=>[a,b,c], y___=>Basic[])
    @test any(d == d1 for d1 in theta)

    subject = [a]
    theta = PM.match_sequence(subject, [x_], sigma, Val{false})
    @test length(collect(theta)) == 1
    
    subject = [a,b,c]
    theta = PM.match_sequence(subject, [x_,b,z_], sigma, Val{false})
    @test length(collect(theta)) == 1
    
    subject = [a,b]
    theta = PM.match_sequence(subject, [x_,y_], sigma, Val{false})
    @test length(collect(theta)) == 1
    
    subject = [a,b,c,a,b,c]
    pattern = [x___,x_, y_, y___]
    theta = PM.match_sequence(subject, pattern, sigma, Val{false})
    d = Dict(x___=>[a], x_=>b, y_=>c,y___=>[a,b,c])
     @test any(d == d1 for d1 in theta)

    subject = Basic[1,2,3,4,3,2,1]
    pattern = [x___,x_, y_, y___]
    theta = PM.match_sequence(subject, pattern, sigma, Val{false})
    theta = Iterators.filter(m -> m[x_] < m[y_], theta)
    for m in theta
        @test m[x_] < m[y_]
    end
    
    
    subject = [a,b,c]
    pattern = [a,b,c]
    theta = PM.match_sequence(subject, pattern, sigma, Val{false})
    @test length(collect(theta)) == 1 && PM.aDict() == collect(theta)[1]  # one match, an empty substitution
    
    subject = Basic[a,b,c,b,a]
    pattern = [x__,c,x__] # no match as [a,b] != [b,a]
    theta = PM.match_sequence(subject, pattern, sigma, Val{false})
    @test isempty(theta)

    subject = Basic[a,b,c,b,a]
    pattern = [x__,b,y___] 
    theta = PM.match_sequence(subject, pattern, sigma, Val{false})
    @test length(collect(theta)) == 2

    
end

@testset "comm=true" begin
    # constants
    sigma = Dict()
    out = PM.match_sequence([a,b,c], [a,b,c], sigma, Val{true})
    # out should be {\phi} (Set((Dict(),))
    @test collect(out)[1] == PM.aDict()

    
    # non-variable
    ss, ps = [sin(a),cos(b),c], [sin(x_),cos(y_),c]
    out = PM.match_sequence(ss, ps, sigma, Val{true})
    @test all([PM.so_far_so_good(ss, ps, sigma) for sigma in out])


    ss, ps = [sin(a),cos(b),c], [sin(x_),cos(y_),c]
    out = PM.match_sequence([sin(a),cos(b),c], [sin(x_),cos(y_),c], Dict(x_=>b), Val{true})
    @test isempty(out)  # x_->a but x_->b...

    ## regular variable
    ss, ps = [a,a,a,a,b,b,c], [x__,x__,y__,y__,z_]
    out = PM.match_sequence(ss, ps, sigma, Val{true})
    @test all([PM.so_far_so_good(ss, ps, sigma) for sigma in out])
    @test length(collect(out)) == 4 # {z->c, x=[a,b],y=a}, {z->c, x->[aa], y->c}...

    ss, ps = [sin(a),cos(b),a, a,a,b,b,c,cos(a^2)], [cos(y_), sin(x_), x_,x_,x_,y_,y_,z_, cos(a^2)]
    out = PM.match_sequence(ss, ps, sigma, Val{true})
    @test all([PM.so_far_so_good(ss, ps, sigma) for sigma in out])
    @test length(collect(out)) == 1 
end


@testset "matches" begin

    ## {} isno match, {Dict()} is a match with no wildcard
    out = matches(a, b)
    @test isempty(out)
    
    out = matches(a,a)
    @test !isempty(out) && isempty(collect(out)[1])

    ## various matches for x
    out = matches(x_, a)
    @test  !isempty(out) && collect(out)[1] == Dict(x_ => a)
    
    out = matches(sin(x_), sin(a))
    @test  !isempty(out) && collect(out)[1] == Dict(x_ => a)

    out = matches([sin(x_)], [sin(a)])
    @test  !isempty(out) && collect(out)[1] == Dict(x_ => a)


    ex = x^4 * exp(x^2)
    ex1 = diff(ex, x,x,x,x,x,x,x,x,x,x)
    out = matches(ex1(x=> x_), ex1)
    @test !isempty(out) && collect(out)[1] == Dict(x_ => x)
    
        
    ## commutative/not
    out = matches([sin(x_), cos(y_)], [cos(b), sin(a)], commutative=false)
    @test isempty(out)

    out = matches([sin(x_), cos(y_)], [cos(b), sin(a)], commutative=true)
    @test !isempty(out)

    
    ## Associative
    out = matches([x_, c], [a,b,c], associative=false)
    @test isempty(out)
    
    out = matches([x_, c], [a,b,c], associative=true)
    @test !isempty(out) && length(collect(out)) == 1
    
    out = matches([x_, x_, y_], [a,a,a,b,b,c], associative=false)
    @test isempty(out)

    out = matches([x_, x_, y_], [a,a,a,b,b,c], associative=true)
    @test !isempty(out)
    
    ## associative -. x_ a plus variable
    out = matches([x_], [a,b,c], associative=false)
    @test  isempty(out) 
    out = matches([x_], [a,b,c], associative=true)  
    @test  !isempty(out) 
    
    
    out = matches(x__ * y_,  a * b * c)
    @test  !isempty(out) && length(collect(out)) == 6 # ch(3,2) + ch(3,1) =
    out = matches(x__ + y_,  a + b + c)
    @test  !isempty(out) && length(collect(out)) == 6 # ch(3,2) + ch(3,1) =
    
    out = matches([x__ * y_,y_], [a, a * b * c], commutative=false)
    @test  isempty(out) 
    out = matches([x__ * y_,y_], [a, a * b * c], commutative=true)
    @test  !isempty(out) && length(collect(out)) == 1 # 
    
    


end
