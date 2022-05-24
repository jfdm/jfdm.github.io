---
title: How we teach Type-Checking is a lie!
tags: idris,type-systems,dependent-types,bidirectional-typing
...


_Well-Typed Programs do not get stuck!_ or so the mantra goes.
A natural question arises of: How do we know that a program is well-typed?
We type-check it!
But what is type-checking?

## Reminder of what type-checking is!

First, we have to realise that types are a way to group related bits of syntax together.
For example, consider this slight variant of Hutton's Razor that supports boolean conjunction as well as addition of natural numbers:

    b ::= True | False
    n ::= 0,1,2,...
    e ::= b | n | (and e e) | (add e e)

In this language terms can be booleans or numbers.
Without types one can construct ill-typed terms, terms that do not make sense:

    (and 0 True)
    (add True 0)

We can use types to group the boolean terms and numerical terms together.
For example, we can type the definition as:

    t : TYPE ::= BOOL | NAT
    n : NAT  ::= 0,1,2,...    | (add e e)
    b : BOOL ::= True | False | (and e e)
    e : t    ::= n | b

We have in-lined the typing rules for brevity, but our definition now describes well-typed terms.
Expanding our example further, we can include let-bound variables:

    t : TYPE ::= BOOL | NAT
    n : NAT  ::= 0,1,2,...    | (add e e)
    b : BOOL ::= True | False | (and e e)
    e : t    ::= v | let v be e in e | n | b

    g : G    ::= Empty | (Extend g (v:t))

To reason about the type of variables we need a typing context to keep track of names given to variables and their type.
With these constructs we can describe type-checking more precisely as:

    g |- e : t

which in simple terms says:

> Given a typing context `g`: Does the term `e` have type `t`?


The typing rules for variables and let-expressions are:

    (v:t) in g
    ========== [ Var ]
    g |- v : t

If the variable `v` with type `t` is in the given context `g` then `v` does have type `t`.

            g        |- e : t
    (Extend g (v:t)) |- b : s
    ======================================= [ Let ]
            g        |- let v be e in b : s

In the context of `g` there is a term `e` of type `t`.
Using let we name `e` as `v` in the body `b` ensuring that the context is extended to let `b` know about `e` as `v`.

## Type-Checking Functions are a lie!

But why is elementary exposition important.
Well how do we realise type-checking in code!?

Well we can realise our terms and types as algebraic data-types:

```idris

data Ty = NAT | BOOL

data Term = N Nat
          | B Bool
          | And Term Term
          | Add Term Term
          | Var String
          | Let String Term Term
```

and then write a type-checker with the form:

```idris
check : (context : List (String, Ty))
     -> (term    : Term)
                -> Either Error Ty
```

where `Error` is a data-type to capture errors such as type-mismatch and variable not found.

The problem is that the function `check` does not look and feel like what a type-checker should do!
It doesn't check if `term` has a type, rather it constructs the type for `term`.
If it can do so.

Here `check` is not a _checking_ function it's a type forming one!
Internally, there will be some checking of types.

## How does type-checking work!?

Let's see how it works:

First, if we encounter a raw value we can directly assert its type:

```idris
check _ (N _) = Just NAT
check _ (B _) = Just BOOL
```

Here we can tell from the term itself what it's type will be.
For the remaining terms we will have to ask (using an application of `check`) what a term's type will be.
Take `And` and `Add`, for each operand we ask what its type is and then check to see if it is the expected type.
Checking fails otherwise.
If both types are correct we can then assert the type of each operation.

```idris
check ctxt (And x y)
  = do BOOL <- check ctxt x | type => Left (Mismatch type BOOL)
       BOOL <- check ctxt y | type => Left (Mismatch type BOOL)
       pure BOOL

check ctxt (Add x y)
  = do NAT <- check ctxt x | type => Left (Mismatch type BOOL)
       NAT <- check ctxt y | type => Left (Mismatch type BOOL)
       pure NAT
```

Similarly, checking variables requires us to ask.
Instead of asking the term, we ask the context!

```idris
check ctxt (Var x)
  = case lookup x ctxt of
      Nothing   => Left (UnknownVar x)
      Just type => Right type
```

Once known we can return the result of the asking.

The last term, `Let`, operates by asking what the type of `this` is.
It then asks, and returns, the type of the body but also extending the typing context.

```idris
check ctxt (Let x this body)
  = do typeX <- check ctxt this
       check ((x,typeX) :: ctxt) body
```

## Communicating the flow of types.

If we look at how types flow in our implementation of `check` you will notice to types of flows:

1. atomic terms present their types when asked; and
2. other terms will do a mixture of:
  1. asking what a sub term's type is; and
  2. asserting what the expected type of a sub-term is.

If you have programmed in Haskell, you will have seen this notion of asking and then asserting from Haskell's ability to perform type inference.
In fact the idea of asking and asserting types from terms has been formalised wonderfully as Bi-Directional Type Theory, and captures nicely the communication between types and terms during the type-checking process.

## Bi-Directional type theory

In bi-directional type-checking types for terms are either:

+ **Synthesised**---constructed from the terms; or
+ **Checked**---checked against the given term.

Below we give the bi-directional typing rules for our language.
We differ from standard notation and use `checks` and `synths` to denote what happens.

First, primitive values:

    ================= [ Nat ]  ================== [ Bool ]
    g |- n checks NAT          g |- b checks BOOL

then `And` and `Add`:

    g |- x checks BOOL                  g |- x checks NAT
    g |- y checks BOOL                  g |- y checks NAT
    ========================== [ And ]  ========================== [ Add ]
    g |- (And x y) checks BOOL          g |- (Add x y) checks BOOL

then Variables:

    (x : t) in g
    =============== [ Var ]
    g |- x synths t

and lastly let-expressions:

            g        |- e synths s
    (Extend g (x:s)) |- b synths t
    =============================== [ Let ]
    g |- (let x be e in b) synths t

## Realising
