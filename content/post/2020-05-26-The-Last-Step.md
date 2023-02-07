---
title: "The Last Step"
tags: ["idris","dependent-types","tdd","musing"]
date: 2020-05-26
---

Every so often I like to reread notable books on /Programming Language Theory/ (PLT).
Namely, one should read:

+ [Programming Language Foundations in Agda](https://plfa.github.io)
+ Software Foundations
+ Types and Programming Languages
+ Practical Foundations for Programming Languages

With these books each presents a treatment of PLT either:
mechanised using Agda or Coq; presented purely theoretically in LaTeX; or
a mixture of theory and practice.

Of particular interest to myself is the presentation using Agda.
Dependent types allow us to present formal descriptions of our programs together with their practical constructions.

I found the treatment in PLFA guilty of missing that last step: How to run one's programming and obtain an result.
This is no fault of the book's authors.
They seek to provide a foundational course towards PLT and they do that fine, unicode and mixfix operators aside.
In fact, Agda programmers can run their programs but what would be more beneficial when presentating a programming language's semantics would be the *last step* and linking this to its practicalities: producing values.

In this post I will show this by considering Hutton's Razor in the dependently-typed language Idris

## Statics

We can define the static semantics of Hutton's Razor as:

```idris
data Term = Val Nat | Add Term Term
```

Terms are either values (natural numbers) or the addition of two terms.
This razor is mono-typed in that all terms have type `Nat`, so we need not be explicit with a term's type:
They are all typed with the same type

## Dynamics

Using these static semantics we can begin to provide straightforward progress and preservation proofs.
If fact we will only look at progress as, given our mono-typed terms typing is *preserved*.
To look at progress we must first define what it means for our terms to reduce.

### Values

Values are our only values:

```idris
data Value : Term -> Type where
  IsValue : {n : Nat} -> Value (Val n)
```

### Reduction

We define reduction on terms using a simple small-step operational semantics.
This can be encoded nicely in Idris using a dependent type as follows:

```idris
data Reduce : (this : Term) -> (that : Term) -> Type where
```

with reduction rules that are focused on the addition term.

#### Left Operands Reduce

Let us start our reduction by stating that left operands can reduce to something.

```idris
   LeftEta : Reduce this that
          -> Reduce (Add this y) (Add that y)
```

### Right Operands Reduce

Once, the left operand is a value and we have proof that the right operand,
then the addition will reduce the right operand.

```idris
   RightEta : Value x
           -> Reduce this that
           -> Reduce (Add x this) (Add x that)
```

### Addition Reduces

If both operands in our term are values then the term can be reduce to a single value.

```idris
   AddBeta : Reduce (Add (Val x) (Val y)) (Val (plus x y))
```

## Progress

With our reduction semantics we can then now look to define progress.

### Definition

Rather straightforwardly, progress is when given a term `t`:

```idris
data Progress : (t : Term) -> Type where
```

we are done when `t` is a value:

```idris
  Done : Value v -> Progress v
```

or we can step through the computation reducing `t` to another term `n`:

```idris
  Step : {n : Term} -> Reduce t n -> Progress t
```

### Proof

using our reduction rules we can describe this progress as given a term `t`:


```idris
progress : (t : Term) -> Progress t
```

#### Values

We are done when we have a value:

```idris
progress (Val k) = Done IsValue
```

#### Addition

Given the addition term we examine the left operand first:


```idris
progress (Add x y) with (progress x)
```

and then the right operand second:


```idris
  progress (Add x y) | (Done z) with (progress y)
```

If both operands are values we can apply `AddBeta` to reduce this to a single value.

```idris
    progress (Add (Val x) (Val y)) | (Done z) | (Done w) = Step AddBeta
```

If we have reduce the left operand but not the right operand we can only reduce using `RightEta`.

```idris
    progress (Add x y) | (Done z) | (Step w) = Step (RightEta w z)
```

'Last' of all if we have *just* reduced the left operand then we apply `LeftEta` to move on to the right one.

```idris
  progress (Add x y) | (Step z) = Step (LeftEta z)

```

## Complete Reduction

We have shown the small step operational semantics with single reductions steps.
To link them together we need to show that a term can reduce down until it can no longer reduce.

More formally speaking we can describe such a set of sequences as a term `this` that will reduce completly to `that`:

```idris
data Reduces : Term -> Term -> Type where
```

The reduction is *reflexive* if reduction doesn't reduce any further:

```idris
  Refl : Reduces t t
```

The reduction is *transitive* in that a term `a` will reduce completly to term `c` if when we know that `a` can take a single step towards term `b`, and that `b` will eventually reduce to term `c`.

```idris
  Trans : Reduce a b -> Reduces b c -> Reduces a c
```

## Finished Evaluation

Evaluation of a term `t` will finish under the following circumstances:

```idris
data Finished : Term -> Type where
```

If the term `t` has reduced to a value we know that the term has been fully normalised---i.e. computed.

```idris
  Normalized : Value t -> Finished t
```

Otherwise, we have a term that is stuck and we can make no more progress.

```idris
  OOF : Finished t
```

## The Last Step(s)

With the definition of our razor and proofs of progress and preservation complete we need to look at evaluating terms.

### For Squigglers.

If we were reading PLFA we will say that given a term `t`:

```idris
data Steps : (t : Term) -> Type where
```

evaluation is a series of steps describing the reduction of `t` to a term `t'` in which `t'` can no longer reduce.


```idris
  MkSteps : Reduces t t' -> Finished t' -> Steps t
```

We can caputure the reduction of a term `t` as a finite set of steps that one must take to either get stuck or, even better, provide a value.

```
eval : Nat -> (t : Term) -> Steps t
```

The natural number here is the *fuel* to allow us to reduce our computation.

```idris
eval Z t = MkSteps Refl OOF
```
If we can no longer take a step we can no longer compute.

```idris
eval (S k) t with (progress t)
```

If not let us compute:

```idris
  eval (S k) t | (Done x) = MkSteps Refl (Normalized x)
```

If we are done computing then great we are finished!

```idris
  eval (S k) t | (Step x) {n} with (eval k n)
```

If not, and we have stepped through once, let us try again.

```idris
    eval (S k) t | (Step x) | (MkSteps y z) = MkSteps (Trans x y) z
```

As we know we can take at least two steps then we are done!

#### Example:

With `eval` we can show that we can compute values from terms.

```
Arith> eval 100 (Add (Val 1) (Val 4))
MkSteps (Trans AddBeta Refl) (Normalized IsValue)
Arith> eval 100 (Add (Val 1) (Add (Val 3) (Val 4)))
MkSteps (Trans (RightEta AddBeta IsValue) (Trans AddBeta Refl)) (Normalized IsValue)
```

It is not clear, however, what this value is.

## For Bodgers.

Let us take a different direction and perform a better last step.
Our definition of evaluation is the same as before:

```idris
data Steps : Term -> Type where
  MkSteps : Inf (Reduces t t') -> Finished t' -> Steps t
```

We now say, however, that our reduction *could* contain infinitly many steps and is possible an infinite data structure.

Rather than use Natural numbers as a source of fuel we can take a different representation, that of the fuel data type:

```idris
data Fuel = Empty | More (Inf Fuel)
```

In which we have no fuel, or infinitly more fuel.

This fuel could also potentialy last forever:

```idris
forever : Fuel
forever = More forever
```

Redefining our evaluation in terms of fuel is straightforward, we swap out Nats for fuel.

```idris
compute : Fuel -> (t : Term) -> Steps t
compute Empty t = MkSteps Refl OOF
compute (More f) t with (progress t)
  compute (More f) t | (Done x) = MkSteps Refl (Normalized x)
  compute (More f) t | (Step x) {n} with (compute f n)
    compute (More f) t | (Step x) | (MkSteps y z) = MkSteps (Trans x y) z
```

With computation defined we can now say how to run a computation:

```idris
run : (t : Term) -> Maybe (n : Nat ** Reduces t (Val n))
```

Our definition of `run` states that a *successful* computation of `t` will tell us the value that is reduced and the set of steps required.
Further, even though we know that computation of `t` is total we nonetheless need to account for the fact that we *might* run out of fuel.
Thus we wrap the result in a maybe type.
With this we look at running the computation:

```idris
run t with (compute forever t)
```

We know that computations can take forever and will either:

```idris
  run t | (MkSteps x (Normalized (IsValue {n}))) = Just (n ** x)
```

produce just a value; or

```idris
  run t | (MkSteps x OOF) = Nothing
```

produce nothing.

With `run` we can now compute values **and** show how they reduce!

```
run (Add (Val 1) (Val 4))
Just (MkDPair 5 (Trans AddBeta Refl))
Arith> run (Add (Val 1) (Add (Val 3) (Val 4)))
Just (MkDPair 8 (Trans (RightEta AddBeta IsValue) (Trans AddBeta Refl)))
```

## Coda.

In this post we have seen:

+ A formal treatment of Hutton's Razor
+ How to write an evaluator for Razor terms that produce values and the steps required to obtain those values.

When using such programs, Idris' erasure will remove the unncessary compile time only computations.

Personaly, I think the addendum of obtaining values and computation steps in the evaluation results makes practical application of PLT in languages such as Agda and Idris that little bit more compeling.
It provides something that is a little bit more tangible that we see in PLFA.
