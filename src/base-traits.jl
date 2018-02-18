module BaseTraits
using SimpleTraits


export IsLeafType, IsBits, IsImmutable, IsContiguous, IsIndexLinear,
       IsAnything, IsNothing, IsCallable, IsIterator

"Trait which contains all types"
@traitdef IsAnything{X}
@traitimpl IsAnything{X} <- (x->true)(X)

"Trait which contains no types"
@traitdef IsNothing{X}
@traitimpl IsNothing{X} <- (x->false)(X)

"Trait of all isbits-types"
@traitdef IsBits{X}
@traitimpl IsBits{X} <- isbits(X)

"Trait of all immutable types"
@traitdef IsImmutable{X}
Base.@pure _isimmutable(X) = !X.mutable
@traitimpl IsImmutable{X}  <- _isimmutable(X)

"Trait of all callable objects"
@traitdef IsCallable{X}
@traitimpl IsCallable{X} <- (X->(X<:Function ||  length(methods(X))>0))(X)

if VERSION<v"0.7-"
    "Trait of all leaf types types"
    @traitdef IsLeafType{X}
    @traitimpl IsLeafType{X} <- isleaftype(X)
else
    export IsConcrete
    "Trait of all concrete types types"
    @traitdef IsConcrete{X}
    @traitimpl IsConcrete{X} <- isconcretetype(X)

    Base.@deprecate_binding IsLeafType IsConcrete
end

"Types which have contiguous memory layout"
@traitdef IsContiguous{X} # https://github.com/JuliaLang/julia/issues/10889
@traitimpl IsContiguous{X} <- Base.iscontiguous(X)

"Array indexing trait."
@traitdef IsIndexLinear{X} # https://github.com/JuliaLang/julia/pull/8432
function isindexlinear(X)
    if IndexStyle(X)==IndexLinear()
        return true
    elseif  IndexStyle(X)==IndexCartesian()
        return false
    else
        error("Not recognized")
    end
end
@traitimpl IsIndexLinear{X} <- isindexlinear(X)

Base.@deprecate_binding IsFastLinearIndex IsIndexLinear

# TODO
## @traitdef IsArray{X} # use for any array like type in the sense of container
##                   # types<:AbstractArray are automatically part

## @traitdef IsMartix{X} # use for any LinearOperator
##                    # types<:AbstractArray are automatically part


"Trait of all iterator types"
@traitdef IsIterator{X}
@generated function SimpleTraits.trait(::Type{IsIterator{X}}) where {X}
    hasmethod(start, Tuple{X}) ? :(IsIterator{X}) : :(Not{IsIterator{X}})
end

end # module
