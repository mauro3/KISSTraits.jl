# Tests that trait dispatch for the BaseTraits does not incur a
# overhead.


# Dict with base-traits to check using value[1] as type and value[2]
# as number of lines allowed in llvm code
cutoff = 5
basetrs = [:IsConcrete=>:Int,
           :IsBits=>:Int,
           :IsImmutable=>:Int,
           :IsContiguous=>:(SubArray{Int64,1,Array{Int64,1},Tuple{Array{Int64,1}},false}),
           :IsIndexLinear=>:(Vector{Int}),
           :IsAnything=>:Int,
           :IsNothing=>:Int,
           :IsCallable=>:(typeof(sin))]


for (bt, tp) in basetrs
    @test @eval @check_fast_traitdispatch $bt $tp true
end
