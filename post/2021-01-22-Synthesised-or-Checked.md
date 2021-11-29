---
title: Synthesised or Checked?
tags: idris,dependent-types,tdd,musing
...

A classic example in the world of dependently typed programming is that of presenting the STLC (and extensions) as well-typed EDSLs.

<!-- idris

import Data.List.Elem

%default total

-->

## The STLC as an Idris EDSL.

Below we give a simple example of the STLC with Booleans.

```idris
data Ty = TyBool | TyFunc Ty Ty

data STLC : (ctxt : List Ty)
         -> (type : Ty)
                 -> Type
  where
    Var : Elem type ctxt -> STLC ctxt type

    Func : (body : STLC (type_param :: ctxt)                    type_body)
                -> STLC                ctxt  (TyFunc type_param type_body)

    App : (func  : STLC ctxt (TyFunc type_param type_body))
       -> (param : STLC ctxt         type_param)
                -> STLC ctxt                    type_body

    B : (b : Bool) -> STLC ctxt TyBool
```

`STLC` is intrinsically well-typed in that, at the type-level, all terms are given a type `type` and has the local typing context.
Within `STLC`, bound variables are represented using *De Bruijn* indices encoded as existential quantification over a type-level context.

## The STLC Formally.

Let us compare this with the formal notation, taken from TAPL, which we present informally.
First we define, names, types, and typing-contexts:

    x         ::= names
    s,t \in T ::= B | s -> t
    g   \in G ::= {} | g + (x:t)

Then we define our expressions:

    b \in B ::= true | false
    e       ::= x | b | (fn x : t . e) | (e $ e)

and our typing rules, which we excluded the introduction rules for Booleans.

First, variables:

    (x : t) \in g
    [ Var ] -----
    g |- x : t

then functions:

    g + (x : s) |- e : t
    [ Func ] -------------------
    g |- (fn x : t . e) : s -> t

and lastly application:

    g |- f : s -> t
    g |- e : s
    [ App ] --------
    g |- (f $ e) : t

Within the formulation, function definitions are explicitly typed.
It is the STLC after all!

An interesting thought, to me at least, is:

> Is `STLC` *as* explicitly typed as the formal notation?

For example, compare:

    ((fn x : Bool . x) $ true)

with

```idris
example : STLC Nil TyBool
example = App (Func (Var Here)) (B True)
```

## Types can be synthesised, or checked.

To beter understand this question, we have to borrow some terminology from Bidirectional type-checking where the types for terms are either:

+ **Synthesised**---types are constructed from the terms; or
+ **Checked**---types are checked against the given term.

We can even give a variant of the bi-directional typing rules, where we replace the standard type annotation `:` with `checks` and `synths`.

First, variables:

    (x : t) \in g
    [ Var ] -----
    g |- x synths t

then functions:

    g + (x : s) |- e checks t
    [ Func ] -------------------
    g |- (fn x : t . e) checks s -> t

and lastly application:

    g |- f synths s -> t
    g |- e checks s
    [ App ] --------
    g |- (f $ e) synths t

What this means is that for function definitions we have to calculate the type of the function body `e` and check it against the presented type.
For function application is, get the type of the function from the function itself, check that the argument `e` has the correct type we generated from `f`, and we can then generate the final type `t`.

## Morally, the `STLC` is not Intrinsically Typed.

So going back to our example `example`, we can reframe the question as:

> Does our encoding of the STLC (`STLC`) synthesis types where instead they should be checked?

The simple question is yes it does, but it depends on context!
Let us now take our example again and have a look at it:

    example : STLC Nil Bool
    example = App (Func (Var Here)) (B true)

Here it's definition is using Idris' type checker to **check** if the body of `example` matches it's type as defined in the type-signature.

Let's now look at the definition of `App`

    App : (func  : STLC ctxt (TyFunc type_param type_body))
       -> (param : STLC ctxt         type_param)
                -> STLC ctxt                    type_body

and compare with the bi-directional version:

    g |- f synths s -> t
    g |- e checks s
    [ App ] --------
    g |- (f $ e) synths t

I contend that unless an expression from `STLC` is bound to an Idris name, it's types will be synthesised rather than checked.
This means that both the types for `func` and `param` (`f` and `e` in the formal notation) are synthesised, constructed from the terms.

Now, let's look at `Func`

    Func : (body : STLC (type_param :: ctxt)                    type_body)
                -> STLC                ctxt  (TyFunc type_param type_body)

and it's bi-directional version:

    g + (x : s) |- e checks t
    [ Func ] -------------------
    g |- (fn x : t . e) checks s -> t

Again, I contend that the types in `Func` are synthesised unless they are bound to an Idris name.

This, to me, means that morally `STLC` is not a *true* realisation of the STLC:

> Types in function definitions are synthesised when they should be checked!

Which means the type you think the function has, might not be the type it actually has!

## We can fix it with value level annotations.

Well the solution is rather simple, we can add an **explicit** type annotation to the definition of `Func`.
For example:

```idris
data TypedSTLC : (ctxt : List Ty)
              -> (type : Ty)
                      -> Type
  where
    Var' : Elem type ctxt -> TypedSTLC ctxt type

    Func' : (type_param : Ty)
         -> (body : TypedSTLC (type_param :: ctxt)                    type_body)
                 -> TypedSTLC                ctxt  (TyFunc type_param type_body)

    App' : (func  : TypedSTLC ctxt (TyFunc type_param type_body))
        -> (param : TypedSTLC ctxt         type_param)
                 -> TypedSTLC ctxt                    type_body

    B' : (b : Bool) -> TypedSTLC ctxt TyBool
```

This gives Idris' type-checker a *source of truth* when synthesising the type of `Func'` and checking the type when `Func'` is used.

Thus our running example is now:

```idris

example' : TypedSTLC Nil TyBool
example' = App' (Func' TyBool (Var' Here)) (B' True)

```

## The End.

PS, this file is a literate Idris2 file ;-)
