---
title: "Thoughts on API Design for Dependently-Typed Languages"
tags: ["idris","type-systems","dependent-types","typing"]
date: 2021-11-29
---

`API` design is an important aspect of Library Design.
Having programmed, for what seems like an age, on personal-ish projects I often do not give this much thought:
I don't have users.
Recently, however, I had a lightbulb type moment when constructing a module for checking that graphs have a certain structural properties.
Now I do not think this moment is special, unique, or something new.
It is an observation:

> Predicates in dependently-typed languages need to be discoverable and enforcable.

Consider, for example, the following predicate of the size of a list:

```idris
data Size : (xs   : List a)
         -> (size : Nat)
                 -> Type
  where
    Empty  : Size Nil Z
    Extend : (rest : Size     xs     k)
                  -> Size (x::xs) (S k)
```

This is a simple structural predicate,
empty lists have length zero, otherwise the size of a list with at least one element is one more than the size of the list we know about.

There are two ways in which we can write a *discovery* function to calculate the predicate's value, and provide proof of this value.
Both require structural recursion to calculate the length.
The first utilises a Dependent Pair as the result stating:
"Given a list `xs` then we can provide the size of `xs`."


```idris
sizeIs : (xs : List a) -> DPair Nat (Size xs)
sizeIs [] = MkDPair Z Zero
sizeIs (x :: xs) with (sizeIs xs)
  sizeIs (x :: xs) | (MkDPair k rest) = MkDPair (S k) (PlusOne rest)
```

We can, however, capitalise on the fact that we can calculate the length of the list using `length`.

```idris
sizeIs : (xs : List a) -> Size xs (length xs)
sizeIs [] = Zero
sizeIs (x :: xs) = PlusOne (sizeIs xs)
```

Here the discovery function is not required to return the value of the length, we know it already.
This function returns the evidence what the size is.
This function does relate to the idea that sometimes we know what the length is but want to check the length.
Perhaps after some transformation on the list.
For such a scenario it would be good to have a second style of function that *enforces* what the length is.
We do so using a function that, given the list and its purported length, decides if the given length matches the length found.

```idris
hasSize : (xs : List a) -> (d : Nat) -> Dec (Size xs d)
hasSize xs d with (xs)
  hasSize xs 0 | [] = Yes Zero
  hasSize xs (S k) | [] = No absurd

  hasSize xs 0 | (x :: ys) = No absurd
  hasSize xs (S k) | (x :: ys) with (hasSize ys k)
    hasSize xs (S k) | (x :: ys) | (Yes prf) = Yes (PlusOne prf)
    hasSize xs (S k) | (x :: ys) | (No contra) = No (\(PlusOne y) => contra y)
```

To help we can describe some `absurd` cases to make the proof a little tidier.

```idris
Uninhabited (Size Nil (S x)) where
  uninhabited Zero impossible
  uninhabited (PlusOne x) impossible

Uninhabited (Size (x::xs) Z) where
  uninhabited Zero impossible
  uninhabited (PlusOne x) impossible

```

With this *one simple trick* we can have, as part of our library API design, important ways in which to work with predicate.
This might be useful if your proofs are required to enforce/discover what a value is.

This idea of enforcing and discovering predicate values is somewhat related to the notion of bi-directional typing in which types are either:
*synthesised*---discovered/constructed/inferred; or
*checked*---enforced/known/checked.
When working in languages with dependent-types (such as Idris) these notions are a nuance that one must remember, or if you are like me one must re-rediscover every so often.
