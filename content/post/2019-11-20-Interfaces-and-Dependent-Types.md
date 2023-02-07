---
title: "On Interfaces and Dependent Types"
tags: ["idris","dependent-types","tdd","musing"]
date: 2019-11-20
---

In this post we will consider the interplay between dependently typed data structures and interfaces.

This post is a literate Idris file so there will be some cruft related to Idris that will remain until I get round to [^1] improving Idris' literate mode support.

    module Main

First we need to hide a few things from the default...



    %hide List
    %default total


Consider the following interface that defines equality for a provided type:


    interface Equals (type : Type) where
      eq : (a,b : type) -> Bool
      notEq : (a,b : type) -> Bool
      notEq a b = not (eq a b)


At first glance there is nothing surprising about its definition.
For example, let us look at the definition of equality for a simple cons-list data type.

    namespace ConsList

Here is the data type:

      data List : (type : Type) -> Type where
        Empty : List type
        Extend : (value : type)
              -> (rest  : List type)
              -> List type


      %name ConsList.List rest, restA, restB


Here is the implementation:

      listEq : Equals type
            => (a,b : List type)
            -> Bool
      listEq Empty               Empty               = True
      listEq Empty               (Extend value rest) = False
      listEq (Extend value rest) Empty               = False
      listEq (Extend value rest) (Extend x restA)    with (eq value x)
        listEq (Extend value rest) (Extend x restA)    | False = False
        listEq (Extend value rest) (Extend x restA)    | True = listEq rest restA

Which we can provide for an `Equals` instance:

    Equals type => Equals (List type) where
      eq = listEq

Great!

Let us now consider 'lists with length', otherwise known as: _Vectors_.

    namespace SizedList

Here is the data type:

      data Vect : (size : Nat) -> (type : Type) -> Type where
         Empty : Vect Z type
         Extend : (value : type)
               -> (rest  : Vect curr type)
               -> Vect (S curr) type

      %name SizedList.Vect rest, restA, restB


Here is an implementation:

      vectEq : Equals type
            => (a,b : Vect size type)
            -> Bool
      vectEq Empty Empty = True
      vectEq (Extend value rest) (Extend x restA) with (eq value x)
        vectEq (Extend value rest) (Extend x restA) | False = False
        vectEq (Extend value rest) (Extend x restA) | True = vectEq rest restA


Which we can provide an `Equals` instance for:

      Equals type => Equals (Vect n type) where
         eq = vectEq

Notice that in the type signature for `vectEq`, and our `Equals`, implementation we have assumed that the compared vectors are of the same length.
We see this with the short hand: `(a,b:...)` in our type signatures.
When we compare vectors, however, it *might be* the case that they are potentially the different sizes, and potentially that they might be the same size.
We need a better implementation.

So let us write one:

       namespace Proper

         vectEq : Equals type
               => (a : Vect sizeA type)
               -> (b : Vect sizeB type)
               -> Bool
         vectEq Empty Empty = True
         vectEq Empty (Extend value rest) = False
         vectEq (Extend value rest) Empty = False
         vectEq (Extend value rest) (Extend x restA) with (eq value x)
           vectEq (Extend value rest) (Extend x restA) | False = False
           vectEq (Extend value rest) (Extend x restA) | True = Proper.vectEq rest restA

Now constructing an `Equals` instance will not result in a type error.

         [alt] Equals type => Equals (Vect size type) where
           eq a b = Proper.vectEq a b

When we call `eq` it will only work with vectors that are the same length.
This is the definition of `Equals`: given two values of the *same* type.
To access the correct implementation we need to call `Proper.vectEq` explicitly, or really just `vectEq`.

The question is to me is:

> Given this one obvious limitations of Interfaces in a dependently
> typed setting are they useful at all for dependently typed
> programming.

In all my years playing with Idris, Interfaces are handy in a few settings:

0. Providing an API to work with structures work on similar data. i.e. `Ord` and `Functor`.
1. when defining operations on single instances of values i.e. `Show`, `Ord`, and `Functor`
2. when composing programs based on the above: `ST`

However, when I write my Idris libraries and Idris programs I find that interfaces are not always the best thing to use.
In fact I shy away from using interfaces unless absolutly necessary.

I think there is a class of interface (of which `Equals` is a prime example, `DecEq` another) where we may need to think a little on their use in a dependently typed setting.

But maybe we need:

    namespace TheFuture
      interface DEquals (ty : idx -> Type) where
        eq : ty a -> ty b -> Bool

        notEq : ty a -> ty b -> Bool
        notEq a b = not (eq a b)


But how do we then shoe horn `Vect` into this...`DEquals (Vect size type) where` will not type check.
We would have to rewrite the type of `Vect` to be `Vect : Type -> Nat -> Type` for it to work, but this itself will cause interfaces such as `Functor` to no longer work...

Idris' support for namespaces alleviates the need for interfaces as it allows one to present similar named constructs and distinguish between them.
But how to ensure that we have consistent names across our code base...

Do we need to rethink interfaces in a dependently typed setting?

The short answer is: I do not know.

I haven't performed a literature review of what the [other team](https://agda.readthedocs.io) are doing or what the other PL people think about it.

Maybe having modules as first class constructs might help, or maybe Idris' support syntactic overloading is intriguing.
By that I mean if you provide implementations for certain operators you get Do-notation and List-notation for free.
I do not mean DSL notation or 'syntax' notation that allows one to produce horrible mix fix unicode abominations that are hard to read.

I might be wrong here, and I am sure several people I know, and many I don't know, will correct me.
But if it was a solved issue, it would have been addressed in Idris2.

[^1]: By round too I mean I have been planning on doing it for half a decade or there about...
---
