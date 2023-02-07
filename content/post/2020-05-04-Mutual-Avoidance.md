---
title: "Mutual Avoidance"
tags: ["idris","dependent-types","tdd","musing"]
date: 2020-05-04
---

Sometimes dependent types push you towards mutually defined data structures:
I try to avoid them where I can.
For me, this occurrs when you need a helper data type where a container is not suitable expressive at the type level to capture the inductive case.
When this happens you can index your helper data structure with the signature of the top type.
This helps remove the need for a mutual
definition, that is turn the call graph edge from undirected to directed.

Here we illustrate the problem and provide a nice solution.

## Preliminaries

First we define some helper containers that exist outside of the example in public libraries but we include here to keep the example self-contained.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> Vect
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> : (<span class="idris-bound">s</span><!-- closing Bound False--> : <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"-->)
           -&gt; (<span class="idris-bound">e</span><!-- closing Bound False--> : <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
           -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->
      <span class="idris-data" title="
Vect 0 a">Empty</span><!-- closing Name Constructor "" "Vect 0 a"--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> <span class="idris-data" title="Zero
Nat">Z</span><!-- closing Name Constructor "Zero" "Nat"--> <span class="idris-bound">a</span><!-- closing Bound False-->
      <span class="idris-data" title="
a -> Vect k a -> Vect (S k) a">Extend</span><!-- closing Name Constructor "" "a -> Vect k a -> Vect (S k) a"--> : (<span class="idris-bound">head</span><!-- closing Bound False--> : <span class="idris-bound">a</span><!-- closing Bound False-->)
            -&gt; (<span class="idris-bound">tail</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> <span class="idris-bound">k</span><!-- closing Bound False--> <span class="idris-bound">a</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">k</span><!-- closing Bound False-->) <span class="idris-bound">a</span><!-- closing Bound False-->
</pre>

A reformulation of a vector of dependent pairs.
Analogous to the forall list quantifier.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> VectD

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> : (<span class="idris-bound">a</span><!-- closing Bound False-->  : <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">e</span><!-- closing Bound False-->  : <span class="idris-bound">a</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">s</span><!-- closing Bound False-->  : <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"-->)
            -&gt; (<span class="idris-bound">as</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">a</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->
      <span class="idris-data" title="
VectD a e 0 Empty">Empty</span><!-- closing Name Constructor "" "VectD a e 0 Empty"--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-data" title="Zero
Nat">Z</span><!-- closing Name Constructor "Zero" "Nat"--> <span class="idris-data" title="
Vect 0 a">Empty</span><!-- closing Name Constructor "" "Vect 0 a"-->
      <span class="idris-data" title="
e v ->
VectD a e k vs -> VectD a e (S k) (Extend v vs)">Extend</span><!-- closing Name Constructor "" "e v ->\nVectD a e k vs -> VectD a e (S k) (Extend v vs)"--> : (<span class="idris-bound">head</span><!-- closing Bound False--> : <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-bound">v</span><!-- closing Bound False-->)
            -&gt; (<span class="idris-bound">tail</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-bound">k</span><!-- closing Bound False--> <span class="idris-bound">vs</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">k</span><!-- closing Bound False-->) (<span class="idris-data" title="
a -> Vect k a -> Vect (S k) a">Extend</span><!-- closing Name Constructor "" "a -> Vect k a -> Vect (S k) a"--> <span class="idris-bound">v</span><!-- closing Bound False--> <span class="idris-bound">vs</span><!-- closing Bound False-->)
</pre>

A reformulation of a vector of dependent pairs but with an added constraint on the parameter/index.
Analogous to the forall list quantifier.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> VectP
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="A reformulation of a vector of dependent pairs but
with an added constraint on the parameter/index.
(a : Type) ->
(a -> Type) ->
(p : a -> Type) ->
(s : Nat) ->
(as : Vect s a) -> VectD a p s as -> Type">VectP</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs but\nwith an added constraint on the parameter/index." "(a : Type) ->\n(a -> Type) ->\n(p : a -> Type) ->\n(s : Nat) ->\n(as : Vect s a) -> VectD a p s as -> Type"--> : (<span class="idris-bound">a</span><!-- closing Bound False-->  : <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">e</span><!-- closing Bound False-->  : <span class="idris-bound">a</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">p</span><!-- closing Bound False-->  : <span class="idris-bound">a</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">s</span><!-- closing Bound False-->  : <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"-->)
            -&gt; (<span class="idris-bound">as</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">a</span><!-- closing Bound False-->)
            -&gt; (<span class="idris-bound">ps</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">p</span><!-- closing Bound False--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">as</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->
</pre>

A reformulation of a vector of dependent pairs.
Analogous to the forall list quantifier.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> ListD
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) -> (a -> Type) -> List a -> Type"--> : (<span class="idris-bound">a</span><!-- closing Bound False-->  : <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">e</span><!-- closing Bound False-->  : <span class="idris-bound">a</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">as</span><!-- closing Bound False--> : <span class="idris-type" title="Generic lists
Type -> Type">List</span><!-- closing Name TypeConstructor "Generic lists" "Type -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->
      <span class="idris-data" title="
ListD a e Empty">Empty</span><!-- closing Name Constructor "" "ListD a e v"--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-data">Nil</span><!-- closing Bound False-->
      <span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> : (<span class="idris-bound">head</span><!-- closing Bound False--> : <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-bound">v</span><!-- closing Bound False-->)
            -&gt; (<span class="idris-bound">tail</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-bound">vs</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> (<span class="idris-bound">v<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::<span class="idris-bound">vs</span><!-- closing Bound False--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Bound False-->)
</pre>

## The Setting

Here we provide the setting in which our problem and solution must exist.


### Meta typing

<pre>
<span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="Meta typing
Type"><span class="idris-type" title="The type of types
Type">Meta</span><!-- closing Name TypeConstructor "The type of types" "Type"--></span><!-- closing Name TypeConstructor "Meta typing" "Type"--> = <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"--> | <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> | <span class="idris-data" title="
Vect (S n) String -> Meta">C</span><!-- closing Name Constructor "" "Vect (S n) String -> Meta"--> (<span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->)
</pre>

### Some important information

<pre>
<span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Type"><span class="idris-type" title="The type of types
Type">Foo</span><!-- closing Name TypeConstructor "The type of types" "Type"--></span><!-- closing Name TypeConstructor "" "Type"-->
</pre>

### Types

<pre>
<span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> : (<span class="idris-bound">meta</span><!-- closing Bound False--> : <span class="idris-type" title="Meta typing
Type">Meta</span><!-- closing Name TypeConstructor "Meta typing" "Type"-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
  <span class="idris-data" title="
Ty A">Alpha</span><!-- closing Name Constructor "" "Ty A"--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->
  <span class="idris-data" title="
Ty A">Oscar</span><!-- closing Name Constructor "" "Ty A"--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->
  <span class="idris-data" title="
Nat -> Ty A -> Ty A">Delta</span><!-- closing Name Constructor "" "Nat -> Ty A -> Ty A"--> : <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"--> -&gt; <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"--> -&gt; <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->

  <span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> : (<span class="idris-bound">s</span><!-- closing Bound False--> : <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->) -&gt; (<span class="idris-bound">foo</span><!-- closing Bound False--> : <span class="idris-type" title="
Type">Foo</span><!-- closing Name TypeConstructor "" "Type"-->) -&gt; (<span class="idris-bound">b</span><!-- closing Bound False--> : <span class="idris-type" title="Boolean Data Type
Type">Bool</span><!-- closing Name TypeConstructor "Boolean Data Type" "Type"-->) -&gt; <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-bound">s</span><!-- closing Bound False-->)

  <span class="idris-data" title="
VectD String (Ty . B) (S n) ss -> Ty (C ss)">Charlie</span><!-- closing Name Constructor "" "VectD String (Ty . B) (S n) ss -> Ty (C ss)"--> : (<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->)
         -&gt; <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
Vect (S n) String -> Meta">C</span><!-- closing Name Constructor "" "Vect (S n) String -> Meta"--> <span class="idris-bound">ss</span><!-- closing Bound False-->)
</pre>

### Context

We define a collection of types as follows.

<pre>
<span class="idris-function" title="We define a collection of types as follows.
List Meta -> Type">Types</span><!-- closing Name Function "We define a collection of types as follows." "List Meta -> Type"--> : <span class="idris-type" title="Generic lists
Type -> Type">List</span><!-- closing Name TypeConstructor "Generic lists" "Type -> Type"--> <span class="idris-type" title="Meta typing
Type">Meta</span><!-- closing Name TypeConstructor "Meta typing" "Type"--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
<span class="idris-function" title="We define a collection of types as follows.
List Meta -> Type">Types</span><!-- closing Name Function "We define a collection of types as follows." "List Meta -> Type"--> = <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-type" title="Meta typing
Type">Meta</span><!-- closing Name TypeConstructor "Meta typing" "Type"--> <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"-->
</pre>

## The Problem

Our problem comes from wanting to establish a predicate over a given
instance of `Types` such that *all* instances of `Bravo` are set to true.

We will call this predicate: `AllTrueBravos`.

The interesting case is not defining a predicate over `Types` but over
a single instance of `Type`. The interesting case is for `Charlie.

We will call the predicate on a single `Type` instance: `AllTrueBravo`.

We begin by defining an instance for `AllTrueBravo` to see what the problem is.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> Problem

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravo</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    ||| Any `A` is true.
    <span class="idris-data" title="Any A is true.
AllTrueBravo a">AnyATrue</span><!-- closing Name Constructor "Any A is true." "AllTrueBravo a"--> : {<span class="idris-bound">a</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->} -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravo</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->

    ||| Bravo is true if the `b` field is `True`.
    <span class="idris-data" title="Bravo is true if the b field is True.
AllTrueBravo (Bravo s foo True)">BravoTrue</span><!-- closing Name Constructor "Bravo is true if the b field is True." "AllTrueBravo (Bravo s foo True)"--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravo</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">foo</span><!-- closing Bound False--> <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->)

    <span class="idris-data" title="
?attempOneRhs -> AllTrueBravo (Charlie cs)">CharlieTrue</span><!-- closing Name Constructor "" "?attempOneRhs -> AllTrueBravo (Charlie cs)"--> : {<span class="idris-bound">ss</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->}
               -&gt; {<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->}
               -&gt; (<span class="idris-bound">prfCSTrue</span><!-- closing Bound False--> : ?attempOneRhs)
               -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravo</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
VectD String (Ty . B) (S n) ss -> Ty (C ss)">Charlie</span><!-- closing Name Constructor "" "VectD String (Ty . B) (S n) ss -> Ty (C ss)"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
</pre>

## Attempt One

A Question: What should the type of `?attempOneRhs` be?

Ideally, we should want to use an instance of `VectP` as that gives us
the type:

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> AttemptOne

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravoA</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    ||| Any `A` is true.
    <span class="idris-data" title="Any A is true.
AllTrueBravoA a">AnyATrue</span><!-- closing Name Constructor "Any A is true." "AllTrueBravoA a"--> : {<span class="idris-bound">a</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->} -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoA</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->

    ||| Bravo is true if the `b` field is `True`.
    <span class="idris-data" title="Bravo is true if the b field is True.
AllTrueBravoA (Bravo s foo True)">BravoTrue</span><!-- closing Name Constructor "Bravo is true if the b field is True." "AllTrueBravoA (Bravo s foo True)"--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoA</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">foo</span><!-- closing Bound False--> <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->)

    <span class="idris-data" title="
VectP String
      (\s => AllTrueBravoA (Bravo s foo True))
      (Ty . B)
      (S n)
      ss
      cs ->
AllTrueBravoA (Charlie cs)">CharlieTrue</span><!-- closing Name Constructor "" "VectP String\n      (\\s => AllTrueBravoA (Bravo s foo True))\n      (Ty . B)\n      (S n)\n      ss\n      cs ->\nAllTrueBravoA (Charlie cs)"--> : {<span class="idris-bound">ss</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->}
               -&gt; {<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->}
               -&gt; (<span class="idris-bound">prfCSTrue</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs but
with an added constraint on the parameter/index.
(a : Type) ->
(a -> Type) ->
(p : a -> Type) ->
(s : Nat) ->
(as : Vect s a) -> VectD a p s as -> Type">VectP</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs but\nwith an added constraint on the parameter/index." "(a : Type) ->\n(a -> Type) ->\n(p : a -> Type) ->\n(s : Nat) ->\n(as : Vect s a) -> VectD a p s as -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->
                                     (\<span class="idris-bound">s</span><!-- closing Bound False--> =&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoA</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">foo</span><!-- closing Bound False--> <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->))
                                     (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->)
                                     (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->)
                                     <span class="idris-bound">ss</span><!-- closing Bound False-->
                                     <span class="idris-bound">cs</span><!-- closing Bound False-->)
               -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoA</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
VectD String (Ty . B) (S n) ss -> Ty (C ss)">Charlie</span><!-- closing Name Constructor "" "VectD String (Ty . B) (S n) ss -> Ty (C ss)"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
</pre>

It type checks! Ship It!

No!

The problem is the unaccounted for `foo`. When you go to write your
decidable procedure, this will cause a unification problem trying to
assert that some foo is equal to another foo, and thus two bravo's
that you know are the same cannot be shown to be the same.


## Attempt Two: A Little Miss-direction can 'help'

Let us attemp to fix the problem by spinning out a definition to
capture `BravoTrue` instances for the `CharlieTrue` case.

Here we will need to define a mutual block to capture two mutually
defined data structures.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> AttempTwo

  <span class="idris-keyword">mutual</span><!-- closing Keyword-->
    <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
String -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "String -> Type"--> : (<span class="idris-bound">s</span><!-- closing Bound False--> : <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
      <span class="idris-data" title="
AllTrueBravoC bravo -> LittleMissDirect s">ApplyLMD</span><!-- closing Name Constructor "" "AllTrueBravoC bravo -> LittleMissDirect s"--> : {<span class="idris-bound">bravo</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-bound">s</span><!-- closing Bound False-->)}
              -&gt; (<span class="idris-bound">prf</span><!-- closing Bound False--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoC</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">bravo</span><!-- closing Bound False-->)
              -&gt; <span class="idris-type" title="
String -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "String -> Type"--> <span class="idris-bound">s</span><!-- closing Bound False-->

    <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravoC</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
         ||| Any `A` is true.
         <span class="idris-data" title="Any A is true.
AllTrueBravoC a">AnyATrue</span><!-- closing Name Constructor "Any A is true." "AllTrueBravoC a"--> : {<span class="idris-bound">a</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->} -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoC</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->

         ||| Bravo is true if the `b` field is `True`.
         <span class="idris-data" title="Bravo is true if the b field is True.
AllTrueBravoC (Bravo s foo True)">BravoTrue</span><!-- closing Name Constructor "Bravo is true if the b field is True." "AllTrueBravoC (Bravo s foo True)"--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoC</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">foo</span><!-- closing Bound False--> <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->)

         <span class="idris-data" title="
VectP String
      LittleMissDirect
      (Ty . B)
      (S n)
      ss
      cs ->
AllTrueBravoC (Charlie cs)">CharlieTrue</span><!-- closing Name Constructor "" "VectP String\n      LittleMissDirect\n      (Ty . B)\n      (S n)\n      ss\n      cs ->\nAllTrueBravoC (Charlie cs)"--> : {<span class="idris-bound">ss</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->}
                    -&gt; {<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->}
                    -&gt; (<span class="idris-bound">prfCSTrue</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs but
with an added constraint on the parameter/index.
(a : Type) ->
(a -> Type) ->
(p : a -> Type) ->
(s : Nat) ->
(as : Vect s a) -> VectD a p s as -> Type">VectP</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs but\nwith an added constraint on the parameter/index." "(a : Type) ->\n(a -> Type) ->\n(p : a -> Type) ->\n(s : Nat) ->\n(as : Vect s a) -> VectD a p s as -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->
                                          (<span class="idris-type" title="
String -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "String -> Type"-->)
                                          (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->)
                                          (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->)
                                          <span class="idris-bound">ss</span><!-- closing Bound False-->
                                          <span class="idris-bound">cs</span><!-- closing Bound False-->)
                    -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoC</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
VectD String (Ty . B) (S n) ss -> Ty (C ss)">Charlie</span><!-- closing Name Constructor "" "VectD String (Ty . B) (S n) ss -> Ty (C ss)"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
</pre>

It type checks! Ship It!

No!

We have the same problem as before.

When you go to write your decidable procedure, the miss direction will
cause a unification problem when working on the `ApplyLMD` pattern for
the `CharlieTrue` cases.

We need to ensure that the 'proofs' on `cs` are applied to `cs` and
that there is no ambiguity. Unificiation will be problematic
otherwise.


## Attempt Three: A Little Miss-direction can 'help' Take 2

Let us attemp to fix the problem by *not* using `VectP` and using a
custom data structrure.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> AttempThree

  <span class="idris-keyword">mutual</span><!-- closing Keyword-->

    <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "VectD String (Ty . B) (S n) ss -> Type"--> : (<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->

      ||| The length is `(S n)` remember.
      <span class="idris-data" title="The length is (S n) remember.
(bravo : Ty (B s)) ->
AllTrueBravoD bravo ->
LittleMissDirect (Extend bravo Empty)">Last</span><!-- closing Name Constructor "The length is (S n) remember." "(bravo : Ty (B s)) ->\nAllTrueBravoD bravo ->\nLittleMissDirect (Extend bravo Empty)"--> : (<span class="idris-bound">bravo</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-bound">s</span><!-- closing Bound False-->))
          -&gt; (<span class="idris-bound">prf</span><!-- closing Bound False--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoD</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">bravo</span><!-- closing Bound False-->)
          -&gt; <span class="idris-type" title="
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "VectD String (Ty . B) (S n) ss -> Type"--> (<span class="idris-data" title="
e v ->
VectD a e k vs -> VectD a e (S k) (Extend v vs)">Extend</span><!-- closing Name Constructor "" "e v ->\nVectD a e k vs -> VectD a e (S k) (Extend v vs)"--> <span class="idris-bound">bravo</span><!-- closing Bound False--> <span class="idris-data" title="
VectD a e 0 Empty">Empty</span><!-- closing Name Constructor "" "VectD a e 0 Empty"-->)

      <span class="idris-data" title="
(bravo : Ty (B s)) ->
AllTrueBravoD bravo ->
LittleMissDirect bravos ->
LittleMissDirect (Extend bravo bravos)">NotLast</span><!-- closing Name Constructor "" "(bravo : Ty (B s)) ->\nAllTrueBravoD bravo ->\nLittleMissDirect bravos ->\nLittleMissDirect (Extend bravo bravos)"--> : (<span class="idris-bound">bravo</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-bound">s</span><!-- closing Bound False-->))
             -&gt; (<span class="idris-bound">prf</span><!-- closing Bound False--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoD</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">bravo</span><!-- closing Bound False-->)
             -&gt; (<span class="idris-bound">rest</span><!-- closing Bound False--> : <span class="idris-type" title="
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "VectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-bound">bravos</span><!-- closing Bound False-->)
             -&gt; <span class="idris-type" title="
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "VectD String (Ty . B) (S n) ss -> Type"--> (<span class="idris-data" title="
e v ->
VectD a e k vs -> VectD a e (S k) (Extend v vs)">Extend</span><!-- closing Name Constructor "" "e v ->\nVectD a e k vs -> VectD a e (S k) (Extend v vs)"--> <span class="idris-bound">bravo</span><!-- closing Bound False--> <span class="idris-bound">bravos</span><!-- closing Bound False-->)

    <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravoD</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
         ||| Any `A` is true.
         <span class="idris-data" title="Any A is true.
AllTrueBravoD a">AnyATrue</span><!-- closing Name Constructor "Any A is true." "AllTrueBravoD a"--> : {<span class="idris-bound">a</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->} -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoD</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->

         ||| Bravo is true if the `b` field is `True`.
         <span class="idris-data" title="Bravo is true if the b field is True.
AllTrueBravoD (Bravo s foo True)">BravoTrue</span><!-- closing Name Constructor "Bravo is true if the b field is True." "AllTrueBravoD (Bravo s foo True)"--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoD</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">foo</span><!-- closing Bound False--> <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->)

         <span class="idris-data" title="
LittleMissDirect cs -> AllTrueBravoD (Charlie cs)">CharlieTrue</span><!-- closing Name Constructor "" "LittleMissDirect cs -> AllTrueBravoD (Charlie cs)"--> : {<span class="idris-bound">ss</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->}
                    -&gt; {<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->}
                    -&gt; (<span class="idris-bound">prfCSTrue</span><!-- closing Bound False--> : <span class="idris-type" title="
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "VectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
                    -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoD</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
VectD String (Ty . B) (S n) ss -> Ty (C ss)">Charlie</span><!-- closing Name Constructor "" "VectD String (Ty . B) (S n) ss -> Ty (C ss)"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
</pre>

However, we are still in a mutual block. Let us parameterise `LittleMissDirect` by the type signature of `AllTrueBravoD` to allow us to remove the need for a mutual block.


## Attempt Four: The Rug that brings it all together

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> TheRug

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
(Ty m -> Type) ->
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "(Ty m -> Type) ->\nVectD String (Ty . B) (S n) ss -> Type"--> : (<span class="idris-bound">allTrueBravo</span><!-- closing Bound False--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
                       -&gt; (<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->)
                       -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->

      ||| The length is `(S n)` remember.
      <span class="idris-data" title="The length is (S n) remember.
(bravo : Ty (B s)) ->
allTrueBravoD bravo ->
LittleMissDirect allTrueBravoD
                 (Extend bravo Empty)">Last</span><!-- closing Name Constructor "The length is (S n) remember." "(bravo : Ty (B s)) ->\nallTrueBravoD bravo ->\nLittleMissDirect allTrueBravoD\n                 (Extend bravo Empty)"--> : (<span class="idris-bound">bravo</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-bound">s</span><!-- closing Bound False-->))
          -&gt; (<span class="idris-bound">prf</span><!-- closing Bound False--> : <span class="idris-bound">allTrueBravoD</span><!-- closing Bound False--> <span class="idris-bound">bravo</span><!-- closing Bound False-->)
          -&gt; <span class="idris-type" title="
(Ty m -> Type) ->
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "(Ty m -> Type) ->\nVectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-bound">allTrueBravoD</span><!-- closing Bound False--> (<span class="idris-data" title="
e v ->
VectD a e k vs -> VectD a e (S k) (Extend v vs)">Extend</span><!-- closing Name Constructor "" "e v ->\nVectD a e k vs -> VectD a e (S k) (Extend v vs)"--> <span class="idris-bound">bravo</span><!-- closing Bound False--> <span class="idris-data" title="
VectD a e 0 Empty">Empty</span><!-- closing Name Constructor "" "VectD a e 0 Empty"-->)

      <span class="idris-data" title="
(bravo : Ty (B s)) ->
allTrueBravoD bravo ->
LittleMissDirect allTrueBravoD bravos ->
LittleMissDirect allTrueBravoD
                 (Extend bravo bravos)">NotLast</span><!-- closing Name Constructor "" "(bravo : Ty (B s)) ->\nallTrueBravoD bravo ->\nLittleMissDirect allTrueBravoD bravos ->\nLittleMissDirect allTrueBravoD\n                 (Extend bravo bravos)"--> : (<span class="idris-bound">bravo</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> (<span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"--> <span class="idris-bound">s</span><!-- closing Bound False-->))
             -&gt; (<span class="idris-bound">prf</span><!-- closing Bound False--> : <span class="idris-bound">allTrueBravoD</span><!-- closing Bound False--> <span class="idris-bound">bravo</span><!-- closing Bound False-->)
             -&gt; (<span class="idris-bound">rest</span><!-- closing Bound False--> : <span class="idris-type" title="
(Ty m -> Type) ->
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "(Ty m -> Type) ->\nVectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-bound">allTrueBravoD</span><!-- closing Bound False--> <span class="idris-bound">bravos</span><!-- closing Bound False-->)
             -&gt; <span class="idris-type" title="
(Ty m -> Type) ->
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "(Ty m -> Type) ->\nVectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-bound">allTrueBravoD</span><!-- closing Bound False--> (<span class="idris-data" title="
e v ->
VectD a e k vs -> VectD a e (S k) (Extend v vs)">Extend</span><!-- closing Name Constructor "" "e v ->\nVectD a e k vs -> VectD a e (S k) (Extend v vs)"--> <span class="idris-bound">bravo</span><!-- closing Bound False--> <span class="idris-bound">bravos</span><!-- closing Bound False-->)

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
       ||| Any `A` is true.
       <span class="idris-data" title="Any A is true.
AllTrueBravoE a">AnyATrue</span><!-- closing Name Constructor "Any A is true." "AllTrueBravoE a"--> : {<span class="idris-bound">a</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-data" title="
Meta">A</span><!-- closing Name Constructor "" "Meta"-->} -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->

       ||| Bravo is true if the `b` field is `True`.
       <span class="idris-data" title="Bravo is true if the b field is True.
AllTrueBravoE (Bravo s foo True)">BravoTrue</span><!-- closing Name Constructor "Bravo is true if the b field is True." "AllTrueBravoE (Bravo s foo True)"--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
(s : String) -> Foo -> Bool -> Ty (B s)">Bravo</span><!-- closing Name Constructor "" "(s : String) -> Foo -> Bool -> Ty (B s)"--> <span class="idris-bound">s</span><!-- closing Bound False--> <span class="idris-bound">foo</span><!-- closing Bound False--> <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->)

       <span class="idris-data" title="
LittleMissDirect AllTrueBravoE cs ->
AllTrueBravoE (Charlie cs)">CharlieTrue</span><!-- closing Name Constructor "" "LittleMissDirect AllTrueBravoE cs ->\nAllTrueBravoE (Charlie cs)"--> : {<span class="idris-bound">ss</span><!-- closing Bound False--> : <span class="idris-type" title="
Nat -> Type -> Type">Vect</span><!-- closing Name TypeConstructor "" "Nat -> Type -> Type"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->}
                  -&gt; {<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->}
                  -&gt; (<span class="idris-bound">prfCSTrue</span><!-- closing Bound False--> : <span class="idris-type" title="
(Ty m -> Type) ->
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "(Ty m -> Type) ->\nVectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
                  -&gt; <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> (<span class="idris-data" title="
VectD String (Ty . B) (S n) ss -> Ty (C ss)">Charlie</span><!-- closing Name Constructor "" "VectD String (Ty . B) (S n) ss -> Ty (C ss)"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)


  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Types ms -> Type">AllTrueBravos</span><!-- closing Name TypeConstructor "" "Types ms -> Type"--> : <span class="idris-function" title="We define a collection of types as follows.
List Meta -> Type">Types</span><!-- closing Name Function "We define a collection of types as follows." "List Meta -> Type"--> <span class="idris-bound">ms</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    <span class="idris-data" title="
AllTrueBravos Empty">Empty</span><!-- closing Name Constructor "" "AllTrueBravos Empty"--> : <span class="idris-type" title="
Types ms -> Type">AllTrueBravos</span><!-- closing Name TypeConstructor "" "Types ms -> Type"--> <span class="idris-data" title="
ListD a e v">Empty</span><!-- closing Name Constructor "" "ListD a e v"-->
    <span class="idris-data" title="
AllTrueBravoE type ->
AllTrueBravos types ->
AllTrueBravos (Extend type types)">Extend</span><!-- closing Name Constructor "" "AllTrueBravoE type ->\nAllTrueBravos types ->\nAllTrueBravos (Extend type types)"--> : (<span class="idris-bound">head</span><!-- closing Bound False--> : <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">type</span><!-- closing Bound False-->)
          -&gt; (<span class="idris-bound">tail</span><!-- closing Bound False--> : <span class="idris-type" title="
Types ms -> Type">AllTrueBravos</span><!-- closing Name TypeConstructor "" "Types ms -> Type"--> <span class="idris-bound">types</span><!-- closing Bound False-->)
          -&gt; <span class="idris-type" title="
Types ms -> Type">AllTrueBravos</span><!-- closing Name TypeConstructor "" "Types ms -> Type"--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">type</span><!-- closing Bound False--> <span class="idris-bound">types</span><!-- closing Bound False-->)
</pre>

## Note

When writing the decision procedure for `littleMissDirect` you will
want to first define the procedure signature for `allTrueBravo` first.


<pre>
<span class="idris-function" title="
(type : Ty m) -> Dec (AllTrueBravoE type)">allTrueBravo</span><!-- closing Name Function "" "(type : Ty m) -> Dec (AllTrueBravoE type)"--> : (<span class="idris-bound">type</span><!-- closing Bound False--> : <span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-bound">m</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="Decidability. A decidable property either holds or
is a contradiction.
Type -> Type">Dec</span><!-- closing Name TypeConstructor "Decidability. A decidable property either holds or\nis a contradiction." "Type -> Type"--> (<span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">type</span><!-- closing Bound False-->)
</pre>

and then realise `littleMissDirect`.

<pre>
<span class="idris-function" title="
(cs : VectD String (Ty . B) (S n) ss) ->
Dec (LittleMissDirect AllTrueBravoE cs)">littleMissDirect</span><!-- closing Name Function "" "(cs : VectD String (Ty . B) (S n) ss) ->\nDec (LittleMissDirect AllTrueBravoE cs)"--> : (<span class="idris-bound">cs</span><!-- closing Bound False--> : <span class="idris-type" title="A reformulation of a vector of dependent pairs.
(a : Type) ->
(a -> Type) -> (s : Nat) -> Vect s a -> Type">VectD</span><!-- closing Name TypeConstructor "A reformulation of a vector of dependent pairs." "(a : Type) ->\n(a -> Type) -> (s : Nat) -> Vect s a -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="Types
Meta -> Type">Ty</span><!-- closing Name TypeConstructor "Types" "Meta -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-data" title="
String -> Meta">B</span><!-- closing Name Constructor "" "String -> Meta"-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">n</span><!-- closing Bound False-->) <span class="idris-bound">ss</span><!-- closing Bound False-->)
                -&gt; <span class="idris-type" title="Decidability. A decidable property either holds or
is a contradiction.
Type -> Type">Dec</span><!-- closing Name TypeConstructor "Decidability. A decidable property either holds or\nis a contradiction." "Type -> Type"--> (<span class="idris-type" title="
(Ty m -> Type) ->
VectD String (Ty . B) (S n) ss -> Type">LittleMissDirect</span><!-- closing Name TypeConstructor "" "(Ty m -> Type) ->\nVectD String (Ty . B) (S n) ss -> Type"--> <span class="idris-type" title="
Ty m -> Type">AllTrueBravoE</span><!-- closing Name TypeConstructor "" "Ty m -> Type"--> <span class="idris-bound">cs</span><!-- closing Bound False-->)
</pre>

and *then* give the procedure body for `allTrueBravos`.

<pre>
<span class="idris-function" title="
(type : Ty m) -> Dec (AllTrueBravoE type)">allTrueBravo</span><!-- closing Name Function "" "(type : Ty m) -> Dec (AllTrueBravoE type)"--> <span class="idris-bound">type</span><!-- closing Bound False--> = ?allTrueBravo_rhs
</pre>

Thus, further removing the need for a mutual block, as you will need `allTrueBravo`.

Not to mention that last of all you will want to give the decision procedure for `allTrueBravos`.

<pre>
<span class="idris-function" title="
(types : Types ms) -> Dec (AllTrueBravos types)">allTrueBravos</span><!-- closing Name Function "" "(types : Types ms) -> Dec (AllTrueBravos types)"--> : (<span class="idris-bound">types</span><!-- closing Bound False--> : <span class="idris-function" title="We define a collection of types as follows.
List Meta -> Type">Types</span><!-- closing Name Function "We define a collection of types as follows." "List Meta -> Type"--> <span class="idris-bound">ms</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="Decidability. A decidable property either holds or
is a contradiction.
Type -> Type">Dec</span><!-- closing Name TypeConstructor "Decidability. A decidable property either holds or\nis a contradiction." "Type -> Type"--> (<span class="idris-type" title="
Types ms -> Type">AllTrueBravos</span><!-- closing Name TypeConstructor "" "Types ms -> Type"--> <span class="idris-bound">types</span><!-- closing Bound False-->)
</pre>
