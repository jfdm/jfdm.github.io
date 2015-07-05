---
title: Dependent Lists
tags: idris,adt,tricks
...

**Edits** Spelling and Grammar

In dependently typed languages such as Idris, types can depend on values. This facilitates the construction of rich type-eco-system for reasoning on our software programmes. However, when working with dependently typed values it makes the collection of these values into containers much more *interesting*. As types depend on a value collecting a set of dependent type into a standard container type means that all items in the container must have the same type.

## An Example

For example, lets take the following dependent type `Foo`, that is parameterised by an enumerated type `FTy`:

```
data FTy = A | B | C

data Foo : FTy -> Type where
   ||| Strings
   FStr   : String -> Foo A
   ||| Naturals
   FNat   : Nat -> Foo B
   ||| Pairs
   FPair  : Foo A -> Foo B -> Foo C
```

The problem comes when we want to collect a set of elements of type `Foo` into a `List`. The type signature/function signature needs the value specified in the type to be given as well. What should the value be that is specified within the type `Foo`?


```
λΠ> with List [FStr "Hello World", FNat 42, FPair (FStr "Hello" (FNat 34))]
(input):1:12:When checking an application of constructor Prelude.List.:::
        Type mismatch between
                Foo B (Type of FNat _)
        and
                Foo A (Expected type)

        Specifically:
                Type mismatch between
                        B
                and
                        A
```

The above example fails as the compiler determines that the type of elements contained within the list is `Foo A`, taken from the first element. However the second element has type `Foo B`, and third `Foo C`.
The question is how to collect lists of dependent types such that the value within the type can differ.

## Solution Zero: Heterogeneous Vectors.

One solution would be to use `HVect`, which allows for collections of arbitrary typed elements to be created. However, this may result in a program that has several unsafe constructs in which the permissible set of elements contained within the list structure is malleable. `HVect` are too loose.

## Solution One: Non-Dependently Typed Wrapper Type

A better more naive solution will be to introduce a secondary wrapper type, say `FNode`, that is explicitly used to collect lists of dependent types specifically for `Foo`.

For example:

```
data FNode = mkNode (Foo x)
```

This can can facilitate lists of the form:


```
fs : List FNode
fs = [mkNode $ FStr "Hello World", mkNode $ FNat 42, mkNode $ FPair (FStr "Hello") (FNat 34)]
```

However, this is cumbersome and requires the programmer having to extract the value from the node, when working with `FNodes` either through pattern matching.
Further, the values within the type are no longer exposed. If you are working at the type level, you have just lost information.

## Solution Two: List of Dependent Pairs

A better approach is to use Dependent Pairs that allow for the value in the type to be more dynamically presented. For example, a list of ``Foo` typed elements type can be specified as:


    fs : List (x ** Foo x)
    fs = [(_ ** FStr "Hello World"), (_ ** FNat 42), (_ ** FPair (FStr "Hello") (FNat 34))]

Notice how the element is comprised of the element and proof that the value n the type exists. More information about dependent pairs [can be found in the Idris manual](http://idris.readthedocs.org/en/latest/tutorial/typesfuns.html#dependent-pairs).
Unfortunately, like the `FNode` solution one has to work with dependent pairs and extract the element from the pair construct. This will result in cumbersome code and lots of `getProof` calls or pattern matching.

## Solution Three: Custom Lists

Idris allows for the creation of custom list structure through overriding both the `Nil` and cons `(::)` constructor. A even better approach will be to create a custom list in Idris that allows for the value in the type to be collected within the type much the same way the values of the elements are also collected.
Allowing for the programmer to gain direct access to the elements that was lost in previous solutions.
For example:

```
data FList : List FTy -> Type where
   Nil  : FList Nil
   (::) : FList x -> FList xs -> FList (x::xs)
```

Allows for:

```
fs : FList [A, B, C]
fs : [FStr "Hello World", FNat 42, FPair (FStr "Hello") (FNat 34)]
```

However, this is a custom list construct for collections of `Foo` elements.
We have now lost access to all HOFs and existing list operations. If we want `FList` to have these operations, they must be constructed explicitly. Secondly for each custom list, distinct operations must also be specified.
There must be a better way...

## Solution Four: Dependent Lists

`DList` is a generalised list-style algebraic data type that allows for a *value* contained within the type to be collected.
Essentially, the `FList` data structure presented above has been generalised.
The definition of `DList` is:

```
data DList : (aTy : Type)
          -> (elemTy : aTy -> Type)
          -> (as : List aTy)
          -> Type where
  Nil  : DList aTy elemTy Nil
  (::) : (elem : elemTy x)
      -> (rest : DList aTy elemTy xs)
      -> DList aTy elemTy (x::xs)
```

Where:

+ `aTy` is the type of the value contained within the list element type.
+ `elemTy` is the type of the elements within the list
+ `as` is the resulting `List` used to contain the different values within the type.


Using this data type we can now provide lists for dependent types collecting a single value from within the type.
For example:

```
fs : DList FTy Foo [A, B, C]
fs = [FStr "Hello World", FNat 42, FPair (FStr "Hello") (FNat 34)]
```

The benefit of this approach is that now a single library of operations involving `DList`s can be specified and developers can create lists of dependent types.
Helaas, with this data structure only one element can be collected from within a type and dependent types that are parameterised using multiple elements must have all but a single value fixed.

A possible work around would be to weaken the relations between the parameters in the type and allow arbitrary values to be collected in the type.

## Summary

Here the `DList` type has been introduced and the reasons behined his construction.
When working with dependent types the `DList` type has been rather helpful in allowing for ease with regards to the collection of lists of dependently typed values.

`DList` can be found in [idris-containers](https://github.com/jfdm/idris-containers).

Future work could be to explore how other more efficient container data types for dependent types can be constructed, for example: Balanced Binary Trees, Dictionaries, and Graphs.
Key to the construction of these data types will be how the values in the types can be collected such that the container's structure can be preserved **and** the values made accessible at the type level.
