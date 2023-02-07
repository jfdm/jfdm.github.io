---
title: "Faking Linear Variable Usage"
tags: ["idris","dependent-types","tdd","musing"]
date: 2021-01-25
---

<!-- idris

import Data.List
import Data.List.Elem

%default total

-->

I have been thinking, [again](https://dblp.uni-trier.de/rec/journals/darts/Muijnck-HughesB20.html), about way's in which one can encode linear variable usage in EDSLs.

## One cannot state usage on things that one cannot bind.

We can encode EDSLs using intrinsically well-typed EDLS that, at the type-level, gives all terms a type `type` and carries around the local typing context.
Bound variables are represented using *De Bruijn* indices encoded as existential quantification over a type-level context.

This traditional approach, however, does not play well with languages that have built in ways to ensure linear variable usage.

Take for example the follow example of the STLC in Idris2.

```idris
data Ty = TyBool | TyFunc Ty Ty

namespace Orig
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

If we want to turn this into the STLC in which variables are only used once then we need to restrict variable usage.

Quantitative Type-Theory is built into Idris2 and we can state such usage on binders as follows:

```idris
double : Num a => (1 x : a) -> a
```

Here the argument `x` to `double` must be used once.

But how can we do this for `STLC`.
Bound things are De Bruijn indexed, and we do not have an explicit binder to state usage on in the EDSL definition itself.

## Let's fake it by explicitly tracking variable usage in the type.

A simple thought occurred to me is that if we are *just* thinking about linear variable usage then we can enhance the definition of `STLC` to explicitly track variable usage.
We do so in four key ways:

0. We change the context to associate each bound type with a usage
1. We further paramterise `STLC` with `old` and `new` contexts that help us track how the context changes wrt to variable usage, and update our type-system accordingly
3. We change the definition of our existential quantifier `Elem` such that each proof updates the usage for the found bound variable
4. We ensure that for functions the parameter passed in *is* used at most once.

Thus our previous EDSL now becomes

```idris
data Usage = USED | FREE

data Item : Type where
  MkItem : Usage -> (ty : Ty) -> Item

data HasItem : Item
            -> List Item -- Old
            -> List Item -- New
            -> Type
  where
    H : HasItem (MkItem FREE ty) (MkItem FREE ty  :: rest) (MkItem USED ty :: rest)
    T : HasItem (MkItem FREE ty)                     rest  rest'
     -> HasItem (MkItem FREE ty) (MkItem x    ty' :: rest) (MkItem x ty' :: rest')

data FakeLSTLC : List Item -- old
         -> List Item -- new
         -> Ty
         -> Type
  where
    Var : HasItem (MkItem FREE ty) old new -> FakeLSTLC old new ty

    Func : (body : FakeLSTLC (MkItem FREE paramTy :: old)
                        (MkItem USED paramTy :: new) bodyTy)
                -> FakeLSTLC old new (TyFunc paramTy bodyTy)

    App : (func  : FakeLSTLC old new  (TyFunc paramTy bodyTy))
       -> (param : FakeLSTLC new new'         paramTy)
                -> FakeLSTLC old new'                 bodyTy

    And : FakeLSTLC old new  TyBool
       -> FakeLSTLC new new' TyBool
       -> FakeLSTLC old new' TyBool

    B : Bool -> FakeLSTLC old old TyBool
```

Notice that:

0. `HasItem` destroys and rebuilds the typing context
1. In the definition of `Func` we ensure that the parameter must be used
2. `And` & `App` threads the context changes through each term
3. `B` doesn't alter the context as it is a pure value

and with this we can write examples:

```idris
example : FakeLSTLC Nil Nil TyBool
example = App (Func (And (B True) (B True))) (B True)
```

fails with:

```sh
1/1: Building 2021-01-25-Fakiing-Linear-Variables (2021-01-25-Fakiing-Linear-Variables.md)
Error: While processing right hand side of example. When
unifying FakeLSTLC (MkItem USED ?paramTy :: ?old) (MkItem USED ?paramTy :: ?old) TyBool and FakeLSTLC (MkItem FREE ?paramTy :: ?old) (MkItem USED ?paramTy :: ?old) TyBool.
Mismatch between: USED and FREE.

2021-01-25-Fakiing-Linear-Variables.md:117:27--117:33
     |
 117 | example = App (Func (And (B True) (B True))) (B True)
     |                           ^^^^^^
```

the variable must be used, but is not.
This example will pass:

```idris
example1 : FakeLSTLC Nil Nil TyBool
example1 = App (Func (And (Var H) (B True))) (B True)
```

This next one will fail because of the duplicate variable usage:

```idris
example2 : FakeLSTLC Nil Nil TyBool
example2 = App (Func (And (Var H) (Var H))) (B True)
```

```sh
Error: While processing right hand side of example2. When
unifying FakeLSTLC (MkItem FREE TyBool :: ?new) (MkItem USED TyBool :: ?new) TyBool and FakeLSTLC (MkItem FREE TyBool :: ?old) (MkItem FREE TyBool :: ?new) TyBool.
Mismatch between: USED and FREE.

2021-01-25-Fakiing-Linear-Variables.md:146:28--146:33
     |
 146 | example2 = App (Func (And (Var H) (Var H))) (B True)
     |                            ^^^^^
```

## Type-Safety

With this approach it might seem a nice and quick way to get linearity in one's EDSL.
The question remains, can this EDSL be used to prove progress for type-safetydate: 2021-01-25-Faking-Linear-Variables.md
---
