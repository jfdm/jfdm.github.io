---
title: Defining Intrinsically Typed Data Structures
tags: idris,dependent-types,tdd,musing
...

When reading foundational texts such as [PLFA](https://plfa.github.io/), [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/), and [Software Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html) the learner is presented with Simply-Typed Lambda Calculi that supports both [products](https://www.ncatlab.org/nlab/show/product+type) and [sums](https://www.ncatlab.org/nlab/show/sum+type).
When translating these calculi to dependently typed languages such [Idris](https://www.idris-lang.org) & Agda, however, how we might approach
supporting other data structures such as tuples, records and variants is not precisely clear.
In fact Software Foundations [*does give an idea*](https://softwarefoundations.cis.upenn.edu/plf-current/Records.html#lab346) on how to do so but let us explore how we may choose to represent such structures in Idris/Agda.

My aim for this post is to:

1. consider how we can construct intrinsically typed data structures for an EDSL in the Idris(2) programming language; and
1. detail an approach to preserve the uniques of variant types.

I am not going to claim that the techniques in this post are new, my literature review of the area is weak, but I wanted to have a public record detailing *my approach* that others can find using the great big search engines floating around cyberspace.

## Background

Before reading this post, I will assume that the reader is familiar with [Part 2 of TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/), may have skimmed [Software Foundations](https://softwarefoundations.cis.upenn.edu/plf-current/index.html), and perused [Part 2 of PLFA](https://plfa.github.io/).

The examples will be in [Idris2](https://www.idris-lang.org) but they should translate to Idris1, and other dependently typed programming languages.

A small caveat, is that I will be discussing the representation of the data types, but have yet to explore their use in reasoning about progress and preservation, nor their use in building a working compiler.
This is for later on in the month.

## The Starting Razor

In this post our starting razor will start as an intrinsically typed expression language that supports let-bindings, and primitive data types representing integers and characters.
We will expand this language to support pairs and sums (their construction, projection, and destruction), before morphing the language to see how we can support tuples, records, and variant types.

Thus, our base types will be:

```{.idris}
data Ty = TyInt | TyChar
```

with the follow combined base syntax/static semantics:

```{.idris}
data Razor : List Ty -> Ty -> Type where
  Var : Elem ty g -> Razor g ty

  Let : (this     : Razor        g  expr)
     -> (beInThis : Razor (expr::g) body)
                 -> Razor        g  body

  I : Int  -> Razor g TyInt
  C : Char -> Razor g TyChar
```

Our razor follows standard constructions used in intrinsically typed interpreters in which variables are De Bruijn indicies realised using the `Elem` list existential quantifier from `Data.List.Elem` that is quantified over a type-level context.

So let's get started.

## Adding Sums and Products

This section will extend our razor with sums and products.

### Types

```{.idris}
data Ty = TyInt | TyChar | TyProd Ty Ty | TySum Ty Ty
```

A product type allows us to pair two structures together, and a sum type to have a structure that contains one of two possible structures.
Thus we extend the definition with two data constructors that pair two type's together.

### Syntax and Static Semantics

We can then extend the definition of our Razor with the following static semantics for data type:

+ **contructors**: for products (`MkPair`); and sums---`Left` & `Right`;
+ **accessors**: for products `First` & `Second`; and
+ **destructors**: for products (`Split`); and sums---`Match`.

So that we now have:

```{.idris}
data Razor : List Ty -> Ty -> Type where
  Var : Elem ty g -> Razor g ty

  Let : (this     : Razor        g  expr)
     -> (beInThis : Razor (expr::g) body)
                 -> Razor        g  body

  I : Int  -> Razor g TyInt
  C : Char -> Razor g TyChar

  MkPair : (left  : Razor g l)
        -> (right : Razor g r)
                 -> Razor g (TyProd l r)

  First  : (pair : Razor g (TyProd l r))
                -> Razor g l

  Second : (pair : Razor g (TyProd l r))
                -> Razor g r

  Split : (pair : Razor g         (TyProd l r))
       -> (body : Razor (r::l::g) b)
               -> Razor g         b

  Left : (left : Razor g        l)
              -> Razor g (TySum l r)

  Right : (right : Razor g          r)
                -> Razor g (TySum l r)

  Match : (variant   : Razor g      (TySum l r))
       -> (whenLeft  : Razor (l::g) b)
       -> (whenRight : Razor (r::g) b)
                    -> Razor g      b

```

### Examples

These definitions follow standard descriptions from PLFA and the like, and we give example instances demonstrating the Razor in action:


#### Pairs

```{.idris}
ab : Razor Nil (TyProd TyInt TyChar)
ab = MkPair (I 1) (C 'c')

a : Razor Nil TyInt
a = First ab

b : Razor Nil TyChar
b = Second ab

ba : Razor Nil (TyProd TyChar TyInt)
ba = Split ab (MkPair (Var Here) (Var $ There Here))

```

#### Sums

```{.idris}
l : Razor Nil (TySum TyChar TyInt)
l = Left (C 'c')

r : Razor Nil (TySum TyChar TyInt)
r = Right (I 1)

lp : Razor Nil (TyProd TyInt TyChar)
lp = Match l (MkPair (I 2) (Var Here)) (MkPair (Var Here) (C 'w'))

rp : Razor Nil (TyProd TyInt TyChar)
rp = Match r (MkPair (I 2) (Var Here)) (MkPair (Var Here) (C 'w'))
```

### We need Type-Ascriptions for Type Unique Sums

Notice that all our examples a statically typed.

A question to remind ourselves about Sum types is what is the type of the scrutinee in the following match expression:

```{.idris}
snip : Razor Nil TyChar
snip = Match (Right (I 1)) (Var Here) (Split (Var Here) (Var Here))
```

Here we have to give a best guess as to what the right type for `(Right (I 1))` is.
We do not have enough information.
Idris2 complains with:

```
ADT.idr:84:20--84:31:While processing right hand side of rfail at ADT.idr:84:5--86:1:
When unifying Razor ?g (TySum ?l TyInt) and Razor [] (TySum TyChar (TyProd ?l TyChar))
Mismatch between:
    TyInt
and
    TyProd ?l TyChar
at:
84      rfail = Match (Right (I 1)) (Var Here) (Split (Var Here) (Var Here))
```

Here Idris2 has worked out that the scruntinee has type `(TySum TyChar (TyProd ?l TyChar))`.
The left case is clearly type char, but the right case is a product type and there is not enough information to work out what the first entry in the pair is.

Software Foundations, and TAPL, suggest that we can make these types unique by providing a full or partial type ascription.

Thus we can attempt to rewrite our data constructor for sum either following the TAPL style:

```{.idris}
  Left : (type: Ty)
      -> (leftValue Razor g tyL)
      -> Razor g type
```

or the Software Foundation style:

```{.idris}
  Left : (tyR : Ty)
      -> (leftValue Razor g tyL)
      -> Razor g (TySum tyL tyR)
```

With the TAPL style we have lost the intrinsic link between the value and its type.
The style for Software Foundation allows us to assert what the missing piece of the sum type is, given that we can work out the type for the left value.

The Software Foundation style requires that we must provide the right type when presenting the left value.
This is okay but doesn't look right and could be construed as counterintuitive: It's the right type but the value is left.
It would be better to provide the full type as in the TAPL style but with the correct static guarantees.
Further, it is interesting to see that within TAPL type-synonym are an aspect of the presented language.

Having type-synonym directly within the Razor itself would be beneficial.
However, as we will see later on we can remedy this problem by introducing data declarations.

But first we will detail how to provide tuples and record first.

## A Razor with Tuples

Tuples improve on pairs by generalising the concept of pairing structures and supports pairing one or more entries together.

### Types

It is important to remember that a tupled has one ore more entries.
We can enforce this by using sized lists (vectors).

```{.idris}
data Ty = TyInt | TyChar
        | TyTuple (Vect (S n) Ty)
```

### Syntax & Static Semantics

With syntax and static semantics we need to be a bit clever.
The data constructor for tuple requires a vector.
We need a data structure (`RazorT`) that allows us to collect one or more razor values at the value level, but also types at the type level.
Naturally, I would use the `All` quantifier (or really my own `DList` variant), however, here we will use a custom data structure.

```{.idris}
data RazorT : List Ty -> Vect (S n) Ty -> Type where
  Singleton : (first : Razor  g ty)
                    -> RazorT g [ty]

  Extend : (third : Razor  g  ty)
        -> (rest  : RazorT g       tys)
                 -> RazorT g (ty:: tys)
```
The type of `RaqzorT` ensures that there are one or more entries that *might* also already exist in a given context.
The constructor `Singleton` represent the **right most** entry in the list i.e. the one with the highest index, and `Extend` appends an entry to the left of an existing tuple.

With `RazorT` we can now extend our Razor with syntax for projection and deconstruction.

```{.idris}
data Razor : List Ty -> Ty -> Type where
  Var : Elem ty g -> Razor g ty

  Let : (this     : Razor        g  expr)
     -> (beInThis : Razor (expr::g) body)
                 -> Razor        g  body

  I : Int  -> Razor g TyInt
  C : Char -> Razor g TyChar

  MkTuple : (values : RazorT g          types)
                   -> Razor  g (TyTuple types)

  Proj : {0 types : Vect (S n) Ty}
      -> (  tuple : Razor g (TyTuple types))
      -> (  idx   : Fin (S n))
                 -> Razor g (index idx types)

  Split : (tuple : Razor g                (TyTuple types))
       -> (body  : Razor (revAdd types g) b)
                -> Razor g                b
```

Taking advantage of vectors we can define a safe projection constructor (`Proj`) that takes as an index a number known to be within the range represented by `[0,S n]`.
The type of `Proj` can then reconstruct the type of the entry using a type-level application of vector's `index` function.

The destructor `Split` decomposes a tuple into its constituent elements i.e. pattern matching.
When augmenting the type of the body of the split we need to add the types of the tupled to the body's context.
Here we use `revAdd : Vect n a -> List a -> List a` to ensure that the elements are added right to left to the existing context.
Thus ensuring that the right most pattern is the last one added to the context.

### Examples

We can see tuples in action here:

#### Definition

```{.idris}
abc : Razor Nil (TyTuple [TyInt, TyChar, TyChar])
abc = MkTuple (Extend (I 1) (Extend (C 'c') (Singleton (C '2'))))
```

#### Projection

```{.idris}
a : Razor Nil (TyInt)
a = Proj abc FZ

b : Razor Nil (TyChar)
b = Proj abc (FS FZ)
```

#### Splitting

```{.idris}
cba : Razor Nil (TyTuple [TyChar, TyChar, TyInt])
cba = Split abc (MkTuple (Extend (Var Here) (Extend (Var (There Here)) (Singleton (Var (There (There Here)))))))
```

Notice that the effect of the `revAdd` as the third entry in the tupled is accessed using `Var Here` (the most recent entry into the context) and the first entry as `Var (There (There Here))`---the third most recent entry.

## The Recorded Razor

We now turn our attention towards Records, otherwise known as named Tuples.
Unsurprisingly, how we represent records does not differ much from tuples.
We need to provide accounting for names.

### Types

Records are named tuples.
When extending our set of types we need to record both the name and the type of at least one entry.
Again vectors help.

```{.idris}
data Ty = TyInt | TyChar
        | TyRecord (Vect (S n) (Pair String Ty))
```

Not that by using a vector we provide no guarantees that the set of labels is actually a set.
Use of a set-like structure would improve the robustness of record definition.

### Syntax and Static Semantics.

Similar to our definition of tuples, we provide a helper data structure to collect the structure's entries.
This time we ensure that both a label and a type are collected.
This is `RazorR`.

```{.idris}
data RazorR : List Ty -> Vect (S n) (Pair String Ty) -> Type where
  Singleton : (label : String)
           -> (value : Razor  g ty)
                   ->  RazorR g [(label, ty)]
  Extend : (label : String)
        -> (value : Razor  g ty)
        -> (rest  : RazorR g kvs)
                 -> RazorR g ((label, ty) :: kvs)
```

Much with the definition of `Tuple` we can replace `RazorR` with a better data structure.

Unsurprisingly, describing record, construction, destruction, and projection follows that for tuples.
The data constructor `MkRecord` creates records using `RazorR`, and `Split` deconstructs records ensuring that the constituent components are available for a given body.
The type-level function, `revAdd` is replaced with `revAdd' : Vect n (String, a) -> List a -> List a`.
Projection of records using `Proj` differs slightly (is simpler) by using existential quantification of the label and type directly to find the corresponding type.

```{.idris}
data Razor : List Ty -> Ty -> Type where
  Var : Elem ty g -> Razor g ty

  Let : (this     : Razor        g  expr)
     -> (beInThis : Razor (expr::g) body)
                 -> Razor        g  body

  I : Int  -> Razor g TyInt
  C : Char -> Razor g TyChar

  MkRecord : (values : RazorR g           types)
                    -> Razor  g (TyRecord types)

  Proj : {0 types : Vect (S n) (Pair String Ty)}
      -> (  rec   : Razor g (TyRecord types))
      -> (  label : String)
      -> (  idx   : Elem (label, type) types)
                 -> Razor g type

  Split : (rec  : Razor g                 (TyRecord types))
       -> (body : Razor (revAdd' types g) b)
               -> Razor g                 b
```

Note that we assume in our record specification that each label is unique.
The existential quantification for `Proj` will select the left-most label and type it finds.
We could improve the definition of Record's type with a **set** to provide guarantees over label uniqueness and leave that as an exercise.

#### Examples

We can show records in action by recreating a simple pair data type as a record.

##### Definition

First we define a record instance:

```{.idris}
pairIC : Razor Nil (TyRecord [("first", TyInt), ("second", TyChar)])
pairIC = MkRecord (Extend "first" (I 1) (Singleton "second" (C 'c')))
```

##### Projection

Then we can project the individual elements within `pairIC`:

```{.idris}
i : Razor Nil TyInt
i = Proj pairIC "first" Here

c : Razor Nil TyChar
c = Proj pairIC "second" (There Here)
```

##### Deconstruction

Finally, we demonstrate deconstruction.

```{.idris}
i' : Razor Nil TyInt
i' = Split pairIC (Var (There Here))

c' : Razor Nil TyChar
c' = Split pairIC (Var (Here))
```

## Unique + Non-Unique Razor Variants

We end this post by looking at two ways to encode variant structures.
The first will be a normal encoding supporting undecided types, and the second will allow for unique types to be given.
Remember that variants are generalised sums that allow for at least one value to be contained.

### Non-Unique Variants,

We begin by looking at non-unique variants.

#### Types

Similar to records, variant types must account for at least one set of labelled values.
What differs is how we treat the values.
Thus the type for variants is the same (aside from different data constructor) as for records:

```{.idris}
data Ty = TyInt | TyChar
        | TyVariant (Vect (S n) (Pair String Ty))
```

Like records our formulation of variants doesn't assume label uniqueness.

#### Syntax & Static Semantics

With records, construction was about pairing a set of values together.
With variants construction is about selecting a value to include.
We represent variants as follows:


```{.idris}
data Razor : List Ty -> Ty -> Type where
  Var : Elem ty g -> Razor g ty

  Let : (this     : Razor        g  expr)
     -> (beInThis : Razor (expr::g) body)
             -> Razor        g  body

  I : Int -> Razor g TyInt
  C : Char -> Razor g TyChar

  Tag : (label : String)
     -> (value : Razor g ty)
     -> (prf   : Elem (label, ty) kvs)
              -> Razor g (TyVariant kvs)

  Match : (value : Razor  g (TyVariant kvs))
       -> (cases : RazorC g kvs b)
                -> Razor  g b
```

Variants are constructed using `Tag` which when given a valid label will associate the value with said label.
Of interest here is `Match`.
Analogous to records and tuples in which we had to collect all fields/entries as these structures pair data together, we must provide a way to examine (discriminate) each valid case in the variant.
We do so using `RazorC`, which we define as:

```{.idris}
data RazorC : List Ty -> Vect (S n) (Pair String Ty) -> Ty -> Type where
  Singleton : (branch : Razor (ty::g) b) -> RazorC g [(label, ty)] b

  Extend : (branch : Razor  (ty::g) b)
        -> (rest   : RazorC g                 kvs  b)
                  -> RazorC g ((label, ty) :: kvs) b
```

The type of `RazorC` is parameterised by:

1. the current typing context;
2. the list of possible cases; and
3. the type of body associated with each possible case.

Note that each body must have the same type.
As with our definitions for `RazorR` and `RazorT` the right-most case is the last case in the variant and we build up the 'patterns' by extending to the left.
For each body associated with a case we ensure that the environment is extended by the appropriate value.


#### Examples

With this definition we can now provide some examples demonstrating use of variants.

##### Construction

Here we construct a variant containing an int or a char.

```{.idris}
ici : Razor Nil (TyVariant [("int", TyInt), ("char", TyChar)])
ici = Tag "int" (I 1) Here

icc : Razor Nil (TyVariant [("int", TyInt), ("char", TyChar)])
icc = Tag "char" (C 'c') (There Here)
```

Notice that much like the original non-unique sum type definition each variant is statically typed.

We can see the error more clearly when destructing variants.

##### Destruction

First we provide some working destructors:

```{.idris}
iciM : Razor Nil TyInt
iciM = Match ici (Extend (Var Here) (Singleton (I 2)))

iccM : Razor Nil TyInt
iccM = Match icc (Extend (Var Here) (Singleton (I 2)))
```

Here is a non-working example:

```{.idris}
fail : Razor Nil TyChar
fail = Let (Tag "int" (I 1) Here) (Match (Var Here) (Extend (C 'c') (Singleton (C 'c'))))
```

that causes Idris2 to complain with:

```
ADT.idr:238:74--238:91:Unsolved holes:
ADT.Variants.Example.{label:5351} introduced at ADT.idr:238:74--238:91
ADT.Variants.Example.{ty:5353} introduced at ADT.idr:238:74--238:91
```

So we need to make these variants unique!

### Unique Variants

For unique variants we need to remind ourselves about how records and variants differ.
Records/tuples have a structure that can be computed from *just* it's values, with unqiue variants we need to know the whole structure prior to constructor.
Thus, as in Software Foundations, we need to be able to **declare** our variants prior to use.
That is we need to introduce data type declarations.

Using our chosen Razor, adding such declarations is straightforward.
We extend the set of types with a new type, the type for variants:

```{.idris}
data Ty = TyInt | TyChar
        | TyVariant (Vect (S n) (Pair String Ty))
        | TyVariantDecl
```

and extend the syntax to include:

1, the variant type construction `Variant` in which we list or fields and types; and
2. an extended `Tag` constructor to incorporate the required ascription.

Matching remains unchanged.

```{.idris}
  Variant : (kvs : Vect (S n) (Pair String Ty))
                -> Razor  g (TyVariantDecl kvs)

  Tag : (label : String)
     -> (value : Razor g ty)
     -> (type  : Razor g (TyVariantDecl))
     -> (prf   : Elem (label, ty) kvs)
              -> Razor g (TyVariant kvs)

```

Done! Job's a good'n or is it...
There are two problems with this approach:

1. Variant declarations cannot included other variant declarations or other declarations we chose to include in the Razor; and
2. The ascription does not intrinsically link the data declaration and data instantiation.

To do so we need to be able to differentiate between different levels of types.
That is the types we use to describe values are different to types that describe the types that describe values.

#### Types

We begin by describing the two levels which we call `Zero` the highest level we use to describing data types, and `One` the next level down which we use to describe values.

```{.idris}
data Level = Zero | One
```

Using these levels, we can now begin to describe our types more accurately:

```{.idris}
data Ty : Level -> Type where
  TyInt  : Ty One
  TyChar : Ty One
  TyVariant : (fields : Vect (S n) (Pair String (Ty One))) -> Ty One

  TyVariantDecl : (fields : Vect (S n) (Pair String (Ty One))) -> Ty Zero
```

The type constructor `TyVariant` describes variant values and is such at level `One` and contains the list of fields and their level one types.
This is expected.
The type constructor `TyVariantDecl` is for describing variant types, this it is at level `Zero`.
However, we need to ensure that we can structurally type-check variant values against variant types.
Thus we also require a list of fields and their corresponding types.

If we were constructring a regular compiler this correspondence wouldn't necessarily be required as we can manually inspect the corresponding syntax for `TyVariantDecl`.

#### Syntax & Static Semantics

Before we can introduce syntax and semantics, we need to rethink our Razor.
The type for types is now dependent on a value.
As with `RazorT` and `RazorR` we need a way to collect dependently typed values.
Naturally, I would use the `All` quantifier (or really my own `DList` variant), however, here we will use a custom data structure to rethink our context and provide existential quantification.

##### Contexts

Contexts require us to collect the levels and the types.

```{.idris}
data Context : List Level -> Type where
  Nil  : Context Nil
  (::) : (type : Ty lvl) -> (rest : Context lvls) -> Context (lvl::lvls)
```

Existential quantification requires us to find the first instance of a value:

```{.idris}
data Elem : (type : Ty lvl) -> (ctxt : Context lvls) -> Type where
  Here : Elem type (type::rest)
  There : (later : Elem type         rest)
                -> Elem type' (type::rest)
```

##### Helper structures

Before we present the syntax we need some helper structures.
To describe variants we need to collect label type pairings, however, we cannot just bundle this as a pair.
We need to ensure that our label type pairing is either a pairing to an irreducible data type, or one that could be previously declared and bound to a name.


```{.idris}
data RazorField : Context lvls -> String -> Ty One -> Type where
   PrimField : (label : String)
            -> (type  : Ty One)
                    -> RazorField g label type

   ComplexField : (label : String)
               -> (type  : Razor      g ty)
                        -> RazorField g label ty
```

An alternative formulation would be to encode this using a data type with a singular constructor and an `Either` type but I chose this construction for a bit more clarity and reduction of type-level computation.

The data type `RazorField` describes a single field.
We still need to collect the separate cases.
Borrowing from how record values are constructed, we can collect fields using as collection.
Here we have constructed a custom data type `RazorD` but `All` (or `DList`) are just as suitable.


```{.idris}
data RazorD : Context lvls -> Vect (S n) (Pair String (Ty One)) -> Type where
  SingletonD : (field : RazorField g label type)
                     -> RazorD     g [(label, type)]

  ExtendD : (field : RazorField g label type)
         -> (rest  : RazorD     g fields)
                  -> RazorD     g ((label, type)::fields)
```

Notice that for both `RazorField` and `RazorD` we index both types with the current typing context.

##### Syntax & Static Semantics.

We can now use these helper data types to declare and construct intrinsically typed variant types

```{.idris}
data Razor : Context lvls -> Ty lvl -> Type where
  Var : Elem ty g -> Razor g ty

  Let : (this     : Razor        g  expr)
     -> (beInThis : Razor (expr::g) body)
                 -> Razor        g  body

  I : Int -> Razor g TyInt
  C : Char -> Razor g TyChar

  Variant : (fields : RazorD g kvs)
                   -> Razor  g (TyVariantDecl kvs)

  Tag : (label : String)
     -> (value : Razor g ty)
     -> (type  : Razor g (TyVariantDecl kvs))
     -> (prf   : Elem (label, ty) kvs)
              -> Razor g (TyVariant kvs)

  Match : (value : Razor  g (TyVariant kvs))
       -> (cases : RazorC g kvs b)
                -> Razor  g b
```

Much of our Razor stays as before, aside from changes to how contexts are defined.
Here `RazorC` is the same definition as before.

The data constructor `Variant` introduces variant type declarations and uses `RazorD` to ensure that its type has the correct structural description.

The data constructor `Tag` introduces variant values with type-ascriptions.
Notice that with how the types for declarations and values are presented we can intrinsically typecheck these variant values!

Now the job is a good'n!

#### Examples

We finish this tutorial with examples:

##### Variant Declaration and Instantiation

We begin with describing a variant type that contains either an int or char value, and use that type to construct a value containing an int using both a let bound definition and directly using Idris.

```{.idris}
iciTy : Razor Nil (TyVariantDecl [("int", TyInt), ("char", TyChar)])
iciTy = Variant (ExtendD (PrimField "int" TyInt) (SingletonD (PrimField "char" TyChar)))

icc : Razor Nil (TyVariant [("int", TyInt), ("char", TyChar)])
icc = Let iciTy $ Tag "char" (C 'c') (Var Here) (There Here)

ici : Razor Nil (TyVariant [("int", TyInt), ("char", TyChar)])
ici = Tag "int" (I 1) iciTy Here
```

##### Matching

Matching follows as before.

```{.idris}
iciM : Razor Nil TyInt
iciM = Match ici (Extend (Var Here) (Singleton (I 2)))

iccM : Razor Nil TyInt
iccM = Match icc (Extend (Var Here) (Singleton (I 2)))
```

## Coda

In this post we:

1. have looked at how we can construct intrinsically typed data structures for an EDSL in the Idris(2) programming language; and
1. detailed an approach to preserve the uniques of variant types.

I do not believe that these techniques are new nor novel.
We borrow existing ideas such as type-levels and use them to our advantage.
Hopefully, someone will see this post and get something from it.

## Where next...

We have describe rather straightforward data types.
Future exploration would be to investigate:

1. [algebraic data types](https://en.wikipedia.org/wiki/Algebraic_data_type) using a singular representation and a singular pattern matching term.
   Algebraic data types are *disjunctions of conjunctions* combining how I've represented variants and adding tuples to the field declaration for each case.
   Note that we cannot expect to use tuples separately *and* as fields as this is not true to how such data type declarations work.
   Each individual field is not projectionable;
1. kinding because why not;
1. polymorphic type because why not; and
1. recursive data types because of the trees and lists.

These provide interesting enough structures to investigate how to reason about them in as part of an EDSL formulation, and get me to reading [some interesting work in formulising System F in Agda](https://doi.org/10.1007/978-3-030-33636-3_10).

Another direction would be to look at a more generic simpler powerful representation of data types as found in Idris' core language TT.
This representation is [inductive families](https://ncatlab.org/nlab/show/inductive+family), and will require [dependent pattern matching](https://doi.org/10.1017/S0956796803004829).
However, I have yet to find time to grok the canonical references (or beginners tutorials) as to how this works in the first place before I attempt it...
I have a back log of references from Idris' journal paper to read about this...and shows gaps in my understanding of dependent type theory and practice...
