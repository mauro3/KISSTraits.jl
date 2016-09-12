# SimpleTraits

[![Build Status](https://travis-ci.org/mauro3/SimpleTraits.jl.svg?branch=master)](https://travis-ci.org/mauro3/SimpleTraits.jl)
[![Build Status](https://ci.appveyor.com/api/projects/status/github/mauro3/SimpleTraits.jl?branch=master&svg=true)](https://ci.appveyor.com/project/mauro3/simpletraits-jl/branch/master)

This package provides a macro-based implementation of traits, using
[Tim Holy's trait trick](https://github.com/JuliaLang/julia/issues/2345#issuecomment-54537633).
The main idea behind traits is to group types outside the
type-hierarchy and to make dispatch work with that grouping.  The
difference to Union-types is that types can be added to a trait after
the creation of the trait, whereas Union types are fixed after
creation.  The cool thing about Tim's trick is that there is no
performance impact compared to using ordinary dispatch.  For a bit of
background and a quick introduction to traits watch my 10min
[JuliaCon 2015](https://youtu.be/j9w8oHfG1Ic) talk.


One good example of the use of traits is the
[abstract array interface](http://docs.julialang.org/en/release-0.5/manual/interfaces/#abstract-arrays)
in Julia-Base.  An abstract array either belongs to the
`Base.LinearSlow` or `Base.LinearFast` trait, depending on how its
internal indexing works.  The advantage to use a trait there is that
one is free to create a type hierarchy independent of this particular
"trait" of the array(s).

Tim Holy
[endorses](https://github.com/mauro3/SimpleTraits.jl/pull/6#issuecomment-236886253)
SimpleTraits, a bit: "I'd say that compared to manually writing out
the trait-dispatch, the "win" is not enormous, but it is a little
nicer."  I suspect that — if you don't write Holy-traits before
breakfast — your "win" should be greater ;-)

# Manual

Traits are defined with `@traitdef`:
```julia
using SimpleTraits
@traitdef IsNice{X}
@traitdef BelongTogether{X,Y} # traits can have several parameters
```
All traits have one or more (type-)parameters to specify the type to
which the trait is applied.  For instance `IsNice{Int}` signifies that
`Int` is a member of `IsNice` (although whether that is true needs to be
checked with the `istrait` function).  Most traits will be
one-parameter traits, however, several parameters are useful when
there is a "contract" between several types.

As a *style convention*, I suggest to use trait names which start with
a verb, as above two traits.  This makes distinguishing between traits
and types easier as type names are usually nouns.

Add types to a trait-group with `@traitimpl`:
```julia
@traitimpl IsNice{Int}
@traitimpl BelongTogether{Int,String}
```

It can be checked whether a type belongs to a trait with `istrait`:
```julia
using Base.Test
@test istrait(IsNice{Int})
@test !istrait(BelongTogether{Int,Int}) # only BelongTogether{Int,String} was added above
```

Functions which dispatch on traits are constructed like:
```julia
@traitfn f{X; IsNice{X}}(x::X) = "Very nice!"
@traitfn f{X; !IsNice{X}}(x::X) = "Not so nice!"
```
This means that a type `X` which is part of the trait `IsNice` will
dispatch to the method returning `"Very nice!"`, otherwise to the one
returning `"Not so nice!"`:
```julia
@test f(5)=="Very nice!"
@test f(5.)=="Not so nice!"
```

Similarly for `BelongTogether` which has two parameters:
```julia
@traitfn f{X,Y; BelongTogether{X,Y}}(x::X,y::Y) = "$x and $y forever!"
@test f(5, "b")=="5 and b forever!"
@test_throws MethodError f(5, 5)

@traitfn f{X,Y; !BelongTogether{X,Y}}(x::X,y::Y) = "$x and $y cannot stand each other!"
@test f(5, 5)=="5 and 5 cannot stand each other!"
```

Note that for a particular generic function, dispatch on traits can only work
on one trait for a given signature.  Continuing above example, this
*does not work* as one may expect:
```julia
@traitdef IsCool{X}
@traitfn f{X; IsCool{X}}(x::X) = "Groovy!"
```
as this definition will just overwrite the definition `@traitfn f{X;
IsNice{X}}(x::X) = 1` from above.  In Julia 0.5 this gives a nice
warning though.

If you need to dispatch on several traits, then you're out of luck.
But please voice your grievance over in pull request
[#2](https://github.com/mauro3/SimpleTraits.jl/pull/2).

## Advanced features

Instead of using `@traitimpl` to add types to traits, it can be
programmed.  Running `@traitimpl IsNice{Int}` essentially expands to
```julia
SimpleTraits.trait{X1 <: Int}(::Type{IsNice{X1}}) = IsNice{X1}
```
I.e. `trait` is the identity function for a fulfilled trait and
returns `Not{TraitInQuestion{...}}` otherwise (this is the fall-back
for `<:Any`).  So instead of using `@traitimpl` this can be coded
directly.  Note that anything but a constant function will probably
not be inlined away by the JIT and will lead to slower dynamic
dispatch.

Example leading to dynamic dispatch:
```julia
@traitdef IsBits{X}
SimpleTraits.trait{X1}(::Type{IsBits{X1}}) = isbits(X1) ? IsBits{X1} : Not{IsBits{X1}}
istrait(IsBits{Int}) # true
istrait(IsBits{Array{Int,1}}) # false
immutable A
    a::Int
end
istrait(IsBits{A}) # true
```

Dynamic dispatch can be avoided using a generated
function (or maybe sometimes `Base.@pure` functions?):
```julia
@traitdef IsBits{X}
@generated function SimpleTraits.trait{X1}(::Type{IsBits{X1}})
    isbits(X1) ? :(IsBits{X1}) : :(Not{IsBits{X1}})
end
```
Note that these programmed-traits can be combined with `@traitimpl`,
i.e. program the general case and add exceptions with `@traitimpl`.

Note also that trait functions can be generated functions:
```julia
@traitfn @generated fg{X; IsNice{X}}(x::X) = (println(x); :x)
```

# Base Traits

I started putting some Julia-Base traits together which can be loaded
with `using SimpleTraits.BaseTraits`, see the source for all
definitions.

Example, dispatch on whether an argument is immutable or not:

```julia
@traitfn f{X; IsImmutable{X}}(x::X) = X(x.fld+1) # make a new instance
@traitfn f{X; !IsImmutable{X}}(x::X) = (x.fld += 1; x) # update in-place

# use
type A; fld end
immutable B; fld end
a=A(1)
f(a) # in-place
@assert a.fld == A(2).fld

b=B(1) # out of place
b2 = f(b)
@assert b==B(1)
@assert b2==B(2)
```

# Background

This package grew out of an attempt to reduce the complexity of
[Traits.jl](https://github.com/mauro3/Traits.jl), but at the same time
staying compatible (but which it isn't).  Compared to Traits.jl, it
drops support for:

- Trait definition in terms of methods and constraints.  Instead the
  user needs to assign types to traits manually.  This removes the
  most complex part of Traits.jl: the checking whether a type
  satisfies a trait definition.
- trait functions which dispatch on more than one trait.  This allows
  to remove the need for generated functions, as well as removing the
  rules for trait-dispatch.

The reason for splitting this away from Traits.jl are:

- creating a more reliable and easier to maintain package than
  Traits.jl
- exploring inclusion in Base (see
  [#13222](https://github.com/JuliaLang/julia/pull/13222)).

My [*JuliaCon 2015*](https://youtu.be/j9w8oHfG1Ic) talk gives a 10
minute introduction to Traits.jl and SimpleTraits.jl.

# Misc

Note that Julia 0.3 is only supported up to tag
[v0.0.1](https://github.com/mauro3/SimpleTraits.jl/tree/v0.0.1).

# References

- [Traits.jl](https://github.com/mauro3/Traits.jl) and its references.
  In particular
  [here](https://github.com/mauro3/Traits.jl#dispatch-on-traits) is an
  in-depth discussion on limitations of Holy-Traits, which this
  package implements.

# To ponder

- There is a big update sitting in the branch
  [m3/multitraits](https://github.com/mauro3/SimpleTraits.jl/pull/2);
  but I never quite finished it.  It would also address the next point:
- Could type inheritance be used for sub-traits
  ([Jutho's idea](https://github.com/JuliaLang/julia/issues/10889#issuecomment-94317470))?
  In particular could it be used in such a way that it is compatible
  with the multiple inheritance used in Traits.jl?
