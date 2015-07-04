---
title: Working With Idris: Long Compile Times
tags: idris,tricks
...

Idris is my day to day language for programming.
This article and subsequent will detail some tricks that may be of benefit when creating Idris Programs.

The Idris compiler goes through many a stage during the compilation process.
Idris code is:

+ elaborated
+ checked for coverage
+ checked for totality
+ checked for unification
+ defunctionalised
+ turned into code

These checks are not necessarily robust and code written in a poor style can lead to false negatives being reported, or the idris compiler becoming confused as to what is happening.

Here are some hand tips for working with Idris.

## Pattern Matching is your friend

Some uses of case split and use of views can lead to long elaboration times, if you use these techniques to interrogate a value on the LHS.
In these cases pattern matching is a better technique here.

essentially, using case split and with/views when pattern matching on
the LHS would have sufficed,

## Namespace disambiguation

Idris allows for syntax overloading.
If you define implementations with named constructors, Idris will allow syntactic sugar to be applied to the resulting data type.

Most notably, if your data type provides an empty list constructor `Nil` and a cons constructor `(::)`, the high-level list notation of `[x,s], []` is automatically available for your data type.
When encountering this notation Idris will attempt to desugar the syntax to a to a normal for i.e. `[x,s]` gets desugared to `(x::s::Nil)`, `[]` to `Nil`
Thus list notation can refer to different types of list depending on the types involved.
If there are multiple styles of list in scope this will cause the elaborator to do more work, as Idris has to work out what type of list you are refering to.

So try to ensure that you disambiguate your code carefully.

One example arose from my use of `unwords` when writing several `Show` instances.
I use `unwords` to automatically insert spaces between elements.
For example:


    data Foobar = MkFoo Int | MkBar Nat

    instance Show Foobar where
      show (MkFoo x) = unwords ["[MkFoo", show x,"]"]
      show (MkBar x) = unwords ["[MkBar", show x,"]"]


Now the `unwords` function has type:

    unwords : List String -> String


When Idris desugars the list notation it cannot work out immediately from the immediate context what type of list it should use.
The use of `unwords` is not enough for Idris to look at the function arguments and discern that it should be the `List` type.
It would be nice if the Idris desugaring fairy could say: 'Hey Buddy, I see you are using some type of list, and that you are passing it as an argument to a function that expects the `List` type. I'll try desugar to that first.'
Instead Idris elaborates on all the possible list types to work out which one to use.
All these checks require effort and will always add to the compilation time.
For minor examples, the overhead is minimal but if Idris has to disambiguate many many many many times then this will increase compilation time.

For this example, a simple means to disambiguate namespaces in function definitions is to use =with= syntax on the RHS.
Note this is not the view pattern.
The above show example will now look like this.

```
  instance Show Foobar where
    show (MkFoo x) = with List unwords ["[MkFoo", show x,"]"]
    show (MkBar x) = with List unwords ["[MkBar", show x,"]"]
```

This is something you should have to do, but we need to at the moment.

Regardless, try to ensure that your code is not unnecessarily ambiguous.
If you turn logging on past level one, then instances of bananna brackets `(||)` will indicate where Idris has to disambiguate things. This can help indicate if you need to disambiguate your code.

It also makes me wonder if Idris should take into account ambiguity of our code, like we take into account totality.
That is, should there be a clarity directive i.e. `%clarity <level>` that allows for a tolerance to be specified over how ambiguous are code can be.

For example:

+ *crystal* There should be no ambiguous operators.
+ *opaque* There can be some level of ambiguity.
+ *muddy*   No restrictions on ambiguous code.

These warnings can then be raised explicitly at compile time as compiler options as we do with `--warnpartial`, and `--total`.
