module SimpleTraits
using MacroTools
const curmod = nameof(@__MODULE__)
import InteractiveUtils

# This is basically just adding a few convenience functions & macros
# around Holy Traits.

export Trait, istrait, @traitdef, @traitimpl, @traitfn, Not, @check_fast_traitdispatch

# All traits are concrete subtypes of this trait.  SUPER is not used
# but present to be compatible with Traits.jl.
## @doc """
## `abstract Trait{SUPER}`

abstract type Trait end #{SUPER}

"""
All Traits are subtypes of abstract type Trait.

A concrete Trait will look like:
```julia
struct Tr1{X,Y} <: Trait end
```
where X and Y are the types involved in the trait.


(SUPER is not used here but in Traits.jl, thus retained for possible
future compatibility.)
"""
Trait

abstract type Not{T<:Trait} <: Trait end

"""
The set of all types not belonging to a trait is encoded by wrapping
it with Not{}, e.g.  Not{Tr1{X,Y}}
"""
Not

# Helper to strip an even number of Not{}s off: Not{Not{T}}->T
stripNot(::Type{T}) where {T<:Trait} = T
stripNot(::Type{Not{T}}) where {T<:Trait} = Not{T}
stripNot(::Type{Not{Not{T}}}) where {T<:Trait} = stripNot(T)

"""
A trait is defined as full-filled if this function is the identity
function for that trait.  Otherwise it returns the trait wrapped in
`Not`.

Example:
```
trait(IsBits{Int}) # returns IsBits{Int}
trait(IsBits{Array}) # returns Not{IsBits{Array}}
```

Usually this function is defined when using the `@traitimpl` macro.

However, instead of using `@traitimpl` one can define a method for
`trait` to implement a trait, see the README.
"""
trait(::Type{T}) where {T<:Trait} = Not{T}
trait(::Type{Not{T}}) where {T<:Trait} = trait(T)

## Under the hood, a trait is then implemented for specific types by
## defining:
#   trait(::Type{Tr1{Int,Float64}}) = Tr1{Int,Float64}
# or
#   trait(::Type{Tr1{I,F}}) where {I<:Integer,F<:FloatingPoint} = Tr1{I,F}
#
# Note due to invariance, this does probably not the right thing:
#   trait(::Type{Tr1{Integer,FloatingPoint}}) = Tr1{Integer, FloatingPoint}

"""
This function checks whether a trait is fulfilled by a specific
set of types.
```
istrait(Tr1{Int,Float64}) => return true or false
```
"""
istrait(::Any) = error("Argument is not a Trait.")
istrait(tr::Type{T}) where {T<:Trait} = trait(tr)==stripNot(tr) ? true : false # Problem, this can run into issue #265
                                                                        # thus is redefine when traits are defined
"""

Used to define a trait.  Traits, like types, are camel cased.  I
suggest to start them with a verb, e.g. `IsImmutable`, to distinguish
them from actual types, which are usually nouns.

Traits need to have one or more (type-)parameters to specify the type
to which the trait is applied.  For instance `IsImmutable{Int}`
signifies that `Int` is part of `IsImmutable` (although whether that
is true needs to be checked with the `istrait` function).  Most traits
will be one-parameter traits, however, several parameters are useful
when there is a "contract" between several types.

Examples:
```julia
@traitdef IsFast{X}
@traitdef IsSlow{X,Y}
```
"""
macro traitdef(tr)
    :(struct $(esc(tr)) <: Trait end)
end

"""
Used to add a type or type-tuple to a trait.  By default a type does
not belong to a trait.

Example:
```julia
@traitdef IsFast{X}
@traitimpl IsFast{Array{Int,1}}
```

Often a trait is dependent on some check-function returning true or
false.  This can be done with:
```julia
@traitimpl IsFast{T} <- isfast(T)
```
where `isfast` is that check-function.

Note that traits implemented with the former of above methods will
override an implementation with the latter method.  Thus it can be
used to define exceptions to the rule.
"""
macro traitimpl(tr)
    if tr.head==:curly || (tr.head==:call && tr.args[1]==:!)
        # makes
        # trait{X1<:Int,X2<:Float64}(::Type{Tr1{X1,X2}}) = Tr1{X1,X2}
        if tr.args[1]==:Not || isnegated(tr)
            tr = tr.args[2]
            negated = true
        else
            negated = false
        end
        typs = tr.args[2:end]
        trname = esc(tr.args[1])
        curly = Any[]
        paras = Any[]
        for (ty,v) in zip(typs, GenerateTypeVars{:upcase}())
            push!(curly, Expr(:(<:), esc(v), esc(ty)))  #:($v<:$ty)
            push!(paras, esc(v))
        end
        arg = :(::Type{$trname{$(paras...)}})
        fnhead = :($curmod.trait($arg) where {$(curly...)})
        isfnhead = :($curmod.istrait($arg) where {$(curly...)})
        if !negated
            return quote
                $fnhead = $trname{$(paras...)}
                nothing
            end
        else
            return quote
                $fnhead = $curmod.Not{$trname{$(paras...)}}
                nothing
            end
        end
    elseif tr.head==:call
        @assert tr.args[1]==:<
        negated,Tr,P1,fn,P2 = @match tr begin
            Not{Tr_{P1__}} <- fn_(P2__) => (true, Tr, P1, fn, P2)
            Tr_{P1__} <- fn_(P2__) => (false, Tr, P1, fn, P2)
        end
        if negated
            fn = Expr(:call, GlobalRef(SimpleTraits, :!), fn)
        end
        return esc(quote
                   function $curmod.trait(::Type{$Tr{$(P1...)}}) where {$(P1...)}
                       return $fn($(P2...)) ? $Tr{$(P1...)} : $curmod.Not{$Tr{$(P1...)}}
                   end
                   nothing
                   end)
    else
        error("Cannot parse $tr")
    end
end

# Defining a function dispatching on the trait (or not)
# @traitfn f(x::X,y::Y) where {X,Y;  Tr1{X,Y}} = ...
# @traitfn f(x::X,y::Y) where {X,Y; !Tr1{X,Y}} = ... # which is just sugar for:
# @traitfn f(x::X,y::Y) where {X,Y; Not{Tr1{X,Y}}} = ...

dispatch_cache = Dict()  # to ensure that the trait-dispatch function is defined only once per pair
let
    global traitfn
    function traitfn(tfn, __module__, __source__)
        # Need
        # f(x::X,Y::Y) where {X,Y} = f(trait(Tr1{X,Y}), x, y)
        # f(::False, x, y)= ...
        if tfn.head==:macrocall
            hasmac = true
            mac = tfn.args[1]
            tfn = tfn.args[3]
        else
            hasmac = false
        end

        # Dissect AST into:
        # fbody: body
        # fname: symbol of name
        # args0: vector of all arguments except wags (without any gensym'ed symbols but stripped of Traitor-traits)
        # args1: like args0 but with gensym'ed symbols where necessary
        # kwargs: all kwargs
        # paras: where-clause parameters
        # typs0: vector of all function parameters (without the trait-ones, no gensym'ed)
        # typs: vector of all function parameters (without the trait-ones, with gensym'ed for Traitor)
        # trait: expression of the trait
        # trait0: expression of the trait without any gensym'ed symbols
        #
        # (The variables without gensym'ed symbols are mostly used for the key of the dispatch cache)

        fhead = tfn.args[1]
        fbody = tfn.args[2]

        # TODO 1.0: remove
        out = @match fhead begin
            f_(args0__; kwargs__)               => (f,[],args0,kwargs)
            f_(args0__)                         => (f,[],args0,[])
            f_(args0__; kwargs__) where paras__ => (f,paras,args0,kwargs)
            f_(args0__) where paras__           => (f,paras,args0,[])
        end
        if out==nothing
            error("Could not parse function-head: $fhead. Note that several `where` are not supported.")
        end
        fname, paras, args0, kwargs = out
        haskwargs = length(kwargs)>0
        # extract parameters and traits from paras and/or args0

        if length(paras)==0
            maybe_traitor = true
        else
            if paras[1] isa Expr && paras[1].head==:parameters
                maybe_traitor = false
                length(paras)<2 && error("Cannot parse function parameters: $para")
                typs = paras[2:end]
                trait = paras[1].args[1]
            elseif paras[1] isa Expr && paras[1].head==:bracescat
                maybe_traitor = false
                length(paras)!=1 && error("Cannot parse function parameters: $para")
                typs = paras[1].args[1:1]
                trait = paras[1].args[2]
            else
                maybe_traitor = true
                # the processing happens below
            end
        end
        if !maybe_traitor
            trait0 = trait # without gensym'ed types, here identical
            typs0 = typs # without gensym'ed types, here identical
            args1 = insertdummy(args0)
        else # This is a Traitor.jl-style function (or invalid).
            # Change typs, trait & args0 into a Traits.jl function.
            # Find the traitor:
            typs0 = deepcopy(paras) # where-clause without gensym'ed types
            typs = paras
            out = nothing
            i = 0 # index of function argument with Traitor trait
            vararg = false
            for outer i in eachindex(args0)
                a = args0[i]
                vararg = a.head==:...
                if vararg
                    a = a.args[1]
                end
                out = @match a begin
                    ::::Tr_           => (nothing,nothing,Tr)
                    ::T_::Tr_         => (nothing,T,Tr)
                    x_Symbol::::Tr_   => (x,nothing,Tr)
                    x_Symbol::T_::Tr_ => (x,T,Tr)
                end
                out!=nothing && break
            end
            out==nothing && error("No trait found in function signature")
            arg,typ,trait0 = out
            if typ===nothing # case `f(x::::Tr)`
                typ = gensym()
                push!(typs, typ)
            elseif length(typs)==0 # case `f(x::Integer::Tr)`
                    # needs to be put into `f(x::I::Tr) where I<:Integer`
                    typ_ = typ
                    typ = gensym()
                    push!(typs, :($typ<:$typ_))
            end
            # Note other cases, e.g.
            # f(x::T::Tr) where T
            # or
            # f(x::Array{T,1}::Tr) where T
            #
            # are handled without doing anything
            if isnegated(trait0)
                trait = :(!($(trait0.args[2]){$typ}))
            else
                trait = :($trait0{$typ})
            end
            args1 = deepcopy(args0)
            if vararg
                args0[i] = arg==nothing ? nothing : :($arg...,).args[1]
                args1[i] = arg==nothing ? :(::$typ...,).args[1] : :($arg::$typ...,).args[1]
            else
                args0[i] = arg==nothing ? nothing : :($arg)
                args1[i] = arg==nothing ? :(::$typ) : :($arg::$typ)
            end
            args1 = insertdummy(args1)
        end # Traitor.jl-style function

        # Process dissected AST
        if isnegated(trait)
            trait0_opposite = trait0 # opposite of `trait` below as that gets stripped of !
            trait = trait.args[2]
            val = :(::Type{$curmod.Not{$trait}})
        else
            trait0_opposite = Expr(:call, :!, trait0)  # generate the opposite
            val = :(::Type{$trait})
        end
        # create the function containing the logic.
        # Note, this is where the line-number should point to.
        head = MacroTools.prewalk(rmlines, :($fname($val, $(strip_kw(args1)...); $(kwargs...)) where {$(typs...)}))
        ex = if hasmac
            Expr(:macrocall, mac, __source__, :($head = $fbody))
        else
            :($head = $fbody)
        end
        # Create the trait dispatch function, if it has not been defined already. Add it to `ex`
        key = (__module__, fname, typs0, strip_kw(args0), trait0_opposite)
        dispatchfn = if !(key ∈ keys(dispatch_cache)) # define trait dispatch function
            dispatch_cache[key] = (haskwargs, args0)
            if !haskwargs
                quote
                    $fname($(args1...)) where {$(typs...)} = (Base.@_inline_meta(); $fname($curmod.trait($trait),
                                                                                           $(strip_tpara(strip_kw(args1))...)
                                                                                           )
                                                              )
                end
            else
                quote
                    $fname($(args1...);kwargs...) where {$(typs...)} = (Base.@_inline_meta(); $fname($curmod.trait($trait),
                                                                                                     $(strip_tpara(strip_kw(args1))...);
                                                                                                     kwargs...
                                                                                                     )
                                                                        )
                end
            end
        else # trait dispatch function already defined
            if dispatch_cache[key][1]!=haskwargs
                return :(error("""
                               Trait-functions can have keyword arguments.
                               But if so, add the same to both `Tr` and `!Tr`, but they can have different default values.
                               """))
            end
            if dispatch_cache[key][2]!=args0
                return :(error("""
                               Trait-functions can have default arguments.
                               But if so, add them to both `Tr` and `!Tr`, and they both need identical values!
                               """))
            end
            delete!(dispatch_cache, key) # permits function redefinition if that's what we want
            nothing # dispatchfn
        end
        return rmlines(quote
                       $dispatchfn
                       Base.@__doc__ $ex
                       end)
    end
end

"""
Defines a function dispatching on a trait. Examples:

```julia
@traitfn f(x::X,y) where {X;  Tr1{X}} = ...
@traitfn f(x::X,y) where {X; !Tr1{X}} = ...

@traitfn f(x::X,y::Y) where {X,Y;  Tr2{X,Y}} = ...
@traitfn f(x::X,y::Y) where {X,Y; !Tr2{X,Y}} = ...
```

Note that the second example is just syntax sugar for `@traitfn f(x::X,y::Y) where {X,Y; Not{Tr1{X,Y}}} = ...`.
"""
macro traitfn(tfn)
    esc(traitfn(tfn, __module__, __source__))
end

######
## Helpers
######

# true if :(!(Tr{x}))
isnegated(t::Expr) = t.head==:call
isnegated(t::Symbol) = false

# [:(x::X)] -> [:x]
# also takes care of :...
strip_tpara(args::Vector) = Any[strip_tpara(a) for a in args]
strip_tpara(a::Symbol) = a
function strip_tpara(a::Expr)
    if a.head==:(::)
        return a.args[1]
    elseif a.head==:...
        return Expr(:..., strip_tpara(a.args[1]))
    elseif a.head==:kw
        @assert length(a.args)==2
        return Expr(:kw, strip_tpara(a.args[1]), a.args[2])
    else
        error("Cannot parse argument: $a")
    end
end


# [:(x::X=4)] -> [:x::X]
# i.e. strips defaults arguments
# also takes care of :...
strip_kw(args::Vector) = Any[strip_kw(a) for a in args]
strip_kw(a) = a
function strip_kw(a::Expr)
    if a.head==:(::) || a.head==:...
        return a
    elseif a.head==:kw
        @assert length(a.args)==2
        return a.args[1]
    else
        error("Cannot parse argument: $a")
    end
end


# insert dummy: ::X -> gensym()::X
# also takes care of :...
# not needed for kwargs
insertdummy(args::Vector) = Any[insertdummy(a) for a in args]
insertdummy(a::Symbol) = a
function insertdummy(a::Expr)
    if a.head==:(::) && length(a.args)==1
        return Expr(:(::), gensym(), a.args[1])
    elseif a.head==:...
        return Expr(:..., insertdummy(a.args[1]))
    else
        return a
    end
end

# generates: X1, X2,... or x1, x2.... (just symbols not actual TypeVar)
struct GenerateTypeVars{CASE} end
Base.iterate(::GenerateTypeVars{:upcase}, state=1) = (Symbol("X$state"), state+1) # X1,..
Base.iterate(::GenerateTypeVars{:lcase}, state=1) = (Symbol("x$state"), state+1)  # x1,...

####
# Annotating the source location
####

function findline(ex::Expr)
    ex.head == :line && return ex
    for a in ex.args
        ret = findline(a)
        isa(ret, Expr) && return ret
    end
    nothing
end
findline(arg) = nothing

####
# Extras
####

# # This does not work.  Errors on compilation with:
# # ERROR: LoadError: UndefVarError: Tr not defined
# function check_traitdispatch(Tr; nlines=5, Args=(Int,))
#     @traitfn fn_test(x::::Tr) = 1
#     @traitfn fn_test(x::::(!Tr)) = 2
#     @assert llvm_lines(fn_test, Args) == nlines
# end


"""
    check_fast_traitdispatch(Tr, Args=(Int,), nlines=6, verbose=false)

Macro to check whether a trait-dispatch is fast (i.e. as fast as an
ordinary function call) or whether dispatch is slow (dynamic).  Only
works with single parameters traits (so far).

Optional arguments are:
- Type parameter to the trait (default `Int`)
- Verbosity (default `false`)

Example:

    @check_fast_traitdispatch IsBits
    @check_fast_traitdispatch IsBits String true

NOTE: This only works when code-coverage is disabled!  Thus, do not
use this macro in tests (or disable `coverage=true` in your
`.travis.yml` script), or it will error.

NOTE: This does not seem to work all the time.  At least in Julia 0.7 this test is
negative for IsIndexLinear, however, it's fast.

TODO: This is rather ugly.  Ideally this would be a function but I ran
into problems, see source code.  Also the macro is ugly.  PRs welcome...
"""
macro check_fast_traitdispatch(Tr, Arg=:Int, verbose=false)
    if Base.JLOptions().code_coverage==1
        @warn "The SimpleTraits.@check_fast_traitdispatch macro only works when running Julia without --code-coverage"
        return nothing
    end
    test_fn = gensym()
    test_fn_null = gensym()
    nl = gensym()
    nl_null = gensym()
    out = gensym()
    esc(quote
        $test_fn_null(x) = 1
        $nl_null = $curmod.llvm_lines($test_fn_null, ($Arg,))
        @traitfn $test_fn(x::::$Tr) = 1
        @traitfn $test_fn(x::::(!$Tr)) = 2
        $nl = $curmod.llvm_lines($test_fn, ($Arg,))
        $out = $nl == $nl_null
        if $verbose && !$out
            println("Number of llvm code lines $($nl) but should be $($nl_null).")
        end
        $out
    end)
end

"Returns number of llvm-IR lines for a call of function `fn` with argument types `args`"
function llvm_lines(fn, args)
    io = IOBuffer()
    InteractiveUtils.code_llvm(io, fn, args)
    #Base.code_native(io, fn, args)
    count(c->c=='\n', String(take!(copy(io))))
end

include("base-traits.jl")

end # module
