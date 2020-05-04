---
title: Decidably Uninformative
tags: idris,dependent-types,tdd,musing
...


Dependently typed theorem proving is about using the power of dependent types to provide guarantees over various properties of software programs and mathematical constructs.
In dependently typed programming we use dependent types to construct and better reason about the properties of our software programs.

While the former requires that we construct proofs, the latter requires that we construct a usable system.
In this post I want to discuss how proving and construction can get in the way of each other and that when programming with dependent types we must recognise and tread carefully the fine line between theorem proving and programming.

## A Helper

To help with our example we need a little helper data structure that I like to use.
This is a reformulation of a list of dependent pairs, and is analogous to the forall list quantifier.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> ListD
  |||
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> : (<span class="idris-bound">a</span><!-- closing Bound False-->  : <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">e</span><!-- closing Bound False-->  : <span class="idris-bound">a</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->)
            -&gt; (<span class="idris-bound">as</span><!-- closing Bound False--> : <span class="idris-type" title="Generic lists
Type -> Type">List</span><!-- closing Name TypeConstructor "Generic lists" "Type -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->
      <span class="idris-data" title="
ListD a e []">Empty</span><!-- closing Name Constructor "" "ListD a e []"--> : <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"-->

      <span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> : (<span class="idris-bound">head</span><!-- closing Bound False--> : <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-bound">v</span><!-- closing Bound False-->)
            -&gt; (<span class="idris-bound">tail</span><!-- closing Bound False--> : <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> <span class="idris-bound">vs</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-bound">a</span><!-- closing Bound False--> <span class="idris-bound">e</span><!-- closing Bound False--> (<span class="idris-bound">v<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::<span class="idris-bound">vs</span><!-- closing Bound False--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Bound False-->)
</pre>

## Setting

Our motivating example will be examining the stopping condition for a simple declarative function-less specificiation language with linear-types.
Within our language a specification can end iff all linear types have been used.

The precise terms, their semantics, and how usage types are represented is irrelevant for this dicsussion.
What is important is how we represent the context and check for the stopping condition.

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> Setting
</pre>

### Usage types

We encode our usage annotations using the following enumerated type.

<pre>
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Type"><span class="idris-type" title="The type of types
Type">Usage</span><!-- closing Name TypeConstructor "The type of types" "Type"--></span><!-- closing Name TypeConstructor "" "Type"--> = <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> | <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> | <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"-->

  <span class="idris-function" title="
(Consumed = Unrestricted) -> Void">notSameCU</span><!-- closing Name Function "" "(Consumed = Unrestricted) -> Void"--> : (<span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"-->) -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
  notSameCU Refl <span class="idris-keyword">impossible</span><!-- closing Keyword-->

  <span class="idris-function" title="
(Free = Unrestricted) -> Void">notSameFU</span><!-- closing Name Function "" "(Free = Unrestricted) -> Void"--> : (<span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"-->) -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
  notSameFU Refl <span class="idris-keyword">impossible</span><!-- closing Keyword-->

  <span class="idris-function" title="
(Consumed = Free) -> Void">notSameCF</span><!-- closing Name Function "" "(Consumed = Free) -> Void"--> : (<span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"-->) -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
  notSameCF Refl <span class="idris-keyword">impossible</span><!-- closing Keyword-->

  <span class="idris-type" title="Decision procedures for propositional equality
Type -> Type"><span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"><span class="idris-function" title="
DecEq Usage"><span class="idris-data" title="
((x1 : t) -> (x2 : t) -> Dec (x1 = x2)) -> DecEq t"><span class="idris-bound"><span class="idris-bound">DecEq <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Constructor "" "((x1 : t) -> (x2 : t) -> Dec (x1 = x2)) -> DecEq t"--></span><!-- closing Name Function "" "DecEq Usage"--></span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--></span><!-- closing Name TypeConstructor "Decision procedures for propositional equality" "Type -> Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
(Consumed = Free) -> Void">notSameCF</span><!-- closing Name Function "" "(Consumed = Free) -> Void"-->)
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
(Consumed = Unrestricted) -> Void">notSameCU</span><!-- closing Name Function "" "(Consumed = Unrestricted) -> Void"-->)
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="The negation of equality is symmetric (follows
from symmetry of equality)
((a = b) -> Void) -> (b = a) -> Void">negEqSym</span><!-- closing Name Function "The negation of equality is symmetric (follows\nfrom symmetry of equality)" "((a = b) -> Void) -> (b = a) -> Void"--> <span class="idris-function" title="
(Consumed = Free) -> Void">notSameCF</span><!-- closing Name Function "" "(Consumed = Free) -> Void"-->)
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
(Free = Unrestricted) -> Void">notSameFU</span><!-- closing Name Function "" "(Free = Unrestricted) -> Void"-->)
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="The negation of equality is symmetric (follows
from symmetry of equality)
((a = b) -> Void) -> (b = a) -> Void">negEqSym</span><!-- closing Name Function "The negation of equality is symmetric (follows\nfrom symmetry of equality)" "((a = b) -> Void) -> (b = a) -> Void"--> <span class="idris-function" title="
(Consumed = Unrestricted) -> Void">notSameCU</span><!-- closing Name Function "" "(Consumed = Unrestricted) -> Void"-->)
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="The negation of equality is symmetric (follows
from symmetry of equality)
((a = b) -> Void) -> (b = a) -> Void">negEqSym</span><!-- closing Name Function "The negation of equality is symmetric (follows\nfrom symmetry of equality)" "((a = b) -> Void) -> (b = a) -> Void"--> <span class="idris-function" title="
(Free = Unrestricted) -> Void">notSameFU</span><!-- closing Name Function "" "(Free = Unrestricted) -> Void"-->)
    <span class="idris-function" title="
(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Usage) -> (x2 : Usage) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
</pre>

### Types

Types will be `A` or `B` types.

<pre>
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Type"><span class="idris-type" title="The type of types
Type">Ty</span><!-- closing Name TypeConstructor "The type of types" "Type"--></span><!-- closing Name TypeConstructor "" "Type"--> = <span class="idris-data" title="
Ty">A</span><!-- closing Name Constructor "" "Ty"--> | <span class="idris-data" title="
Ty">B</span><!-- closing Name Constructor "" "Ty"-->

  <span class="idris-function" title="
(A = B) -> Void">notSameAB</span><!-- closing Name Function "" "(A = B) -> Void"--> : (<span class="idris-data" title="
Ty">A</span><!-- closing Name Constructor "" "Ty"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
Ty">B</span><!-- closing Name Constructor "" "Ty"-->) -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
  notSameAB Refl <span class="idris-keyword">impossible</span><!-- closing Keyword-->

  <span class="idris-type" title="Decision procedures for propositional equality
Type -> Type"><span class="idris-function" title="
(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)"><span class="idris-function" title="
DecEq Ty"><span class="idris-data" title="
((x1 : t) -> (x2 : t) -> Dec (x1 = x2)) -> DecEq t"><span class="idris-bound"><span class="idris-bound">DecEq <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Constructor "" "((x1 : t) -> (x2 : t) -> Dec (x1 = x2)) -> DecEq t"--></span><!-- closing Name Function "" "DecEq Ty"--></span><!-- closing Name Function "" "(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)"--></span><!-- closing Name TypeConstructor "Decision procedures for propositional equality" "Type -> Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    <span class="idris-function" title="
(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Ty">A</span><!-- closing Name Constructor "" "Ty"--> <span class="idris-data" title="
Ty">A</span><!-- closing Name Constructor "" "Ty"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
    <span class="idris-function" title="
(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Ty">A</span><!-- closing Name Constructor "" "Ty"--> <span class="idris-data" title="
Ty">B</span><!-- closing Name Constructor "" "Ty"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> <span class="idris-function" title="
(A = B) -> Void">notSameAB</span><!-- closing Name Function "" "(A = B) -> Void"-->
    <span class="idris-function" title="
(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Ty">B</span><!-- closing Name Constructor "" "Ty"--> <span class="idris-data" title="
Ty">A</span><!-- closing Name Constructor "" "Ty"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="The negation of equality is symmetric (follows
from symmetry of equality)
((a = b) -> Void) -> (b = a) -> Void">negEqSym</span><!-- closing Name Function "The negation of equality is symmetric (follows\nfrom symmetry of equality)" "((a = b) -> Void) -> (b = a) -> Void"--> <span class="idris-function" title="
(A = B) -> Void">notSameAB</span><!-- closing Name Function "" "(A = B) -> Void"-->)
    <span class="idris-function" title="
(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)">decEq</span><!-- closing Name Function "" "(x1 : Ty) -> (x2 : Ty) -> Dec (x1 = x2)"--> <span class="idris-data" title="
Ty">B</span><!-- closing Name Constructor "" "Ty"--> <span class="idris-data" title="
Ty">B</span><!-- closing Name Constructor "" "Ty"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
</pre>

### Context

We simply describe the context as a list of name type usage pairings.

<pre>
  <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"--> : <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
  <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"--> = <span class="idris-type" title="Generic lists
Type -> Type">List</span><!-- closing Name TypeConstructor "Generic lists" "Type -> Type"--> <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">(<span class="idris-type" title="Strings in some unspecified encoding
Type">String<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--></span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">)</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"-->

</pre>

## The Problem: Accounting for freedom.

Our problem is that we want to ensure that our type-level stopping condition requires that all bound terms in our typing context have been used.

We first see how using a typically straight forward approach leads to a valid program that is not informative for describing what is wrong.

Rather trivially we can represent this as a deciable test on the context.

### Stating that Items are used.

First, we describe a predicate to describe in an entry in our context is used:

<pre>
<span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> : (<span class="idris-bound">item</span><!-- closing Bound False--> : <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
</pre>

If the item is linear it must be 'consumed'.

<pre>
  <span class="idris-data" title="
ItemIsUsed (label, ty, Consumed)">Linear</span><!-- closing Name Constructor "" "ItemIsUsed (label, ty, Consumed)"--> : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">label<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">ty<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Consumed<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"-->
</pre>

If the item has unrestricted usage, it has been used.

<pre>
  <span class="idris-data" title="
ItemIsUsed (label, ty, Unrestricted)">Unbound</span><!-- closing Name Constructor "" "ItemIsUsed (label, ty, Unrestricted)"--> : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">label<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">ty<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Unrestricted<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"-->
</pre>

With `ItemIsUsed` we can show that a Free variable cannot have neen used:

<pre>
<span class="idris-function" title="
ItemIsUsed (label, ty, Free) -> Void">isAmerican</span><!-- closing Name Function "" "ItemIsUsed (label, ty, Free) -> Void"--> : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">label<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-bound">ty<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
isAmerican Linear <span class="idris-keyword">impossible</span><!-- closing Keyword-->
isAmerican Unbound <span class="idris-keyword">impossible</span><!-- closing Keyword-->
</pre>


We can use this 'fact' to write a decision procedure that given an item in our context tells us if it has been used or not.

<pre>
<span class="idris-function" title="
(item : (String, Ty, Usage)) ->
Dec (ItemIsUsed item)">itemIsUsed</span><!-- closing Name Function "" "(item : (String, Ty, Usage)) ->\nDec (ItemIsUsed item)"--> : (<span class="idris-bound">item</span><!-- closing Bound False--> : <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) -&gt; <span class="idris-type" title="Decidability. A decidable property either holds or
is a contradiction.
Type -> Type">Dec</span><!-- closing Name TypeConstructor "Decidability. A decidable property either holds or\nis a contradiction." "Type -> Type"--> (<span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-bound">item</span><!-- closing Bound False-->)
itemIsUsed (label, (ty, use)) <span class="idris-keyword"><span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsUsed (label, ty, warg))"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-bound">use</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsUsed (label, ty, warg))"--></span><!-- closing Keyword-->
  <span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsUsed (label, ty, warg))">itemIsUsed</span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsUsed (label, ty, warg))"--> (<span class="idris-bound">label</span><!-- closing Bound False-->, (<span class="idris-bound">ty</span><!-- closing Bound False-->, <span class="idris-bound">use</span><!-- closing Bound False-->)) | <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="
ItemIsUsed (label, ty, Consumed)">Linear</span><!-- closing Name Constructor "" "ItemIsUsed (label, ty, Consumed)"-->
  <span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsUsed (label, ty, warg))">itemIsUsed</span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsUsed (label, ty, warg))"--> (<span class="idris-bound">label</span><!-- closing Bound False-->, (<span class="idris-bound">ty</span><!-- closing Bound False-->, <span class="idris-bound">use</span><!-- closing Bound False-->)) | <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
ItemIsUsed (label, ty, Free) -> Void">isAmerican</span><!-- closing Name Function "" "ItemIsUsed (label, ty, Free) -> Void"-->)
  <span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsUsed (label, ty, warg))">itemIsUsed</span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsUsed (label, ty, warg))"--> (<span class="idris-bound">label</span><!-- closing Bound False-->, (<span class="idris-bound">ty</span><!-- closing Bound False-->, <span class="idris-bound">use</span><!-- closing Bound False-->)) | <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="
ItemIsUsed (label, ty, Unrestricted)">Unbound</span><!-- closing Name Constructor "" "ItemIsUsed (label, ty, Unrestricted)"-->
</pre>

### Stating that contexts have been used.

Using `ListD` we can then provide quantification over a context stating that **ALL** items have been used.

<pre>
<span class="idris-function" title="
Context -> Type">AllUsed</span><!-- closing Name Function "" "Context -> Type"--> : (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
<span class="idris-function" title="
Context -> Type">AllUsed</span><!-- closing Name Function "" "Context -> Type"--> = <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"-->
</pre>

The decision procedure to check if a context has been used is straightforward.

If the head is free then the context has not all been used.

<pre>
<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> : (<span class="idris-bound">contra</span><!-- closing Bound False--> : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-bound">x</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->)
              -&gt; <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">(<span class="idris-type" title="Strings in some unspecified encoding
Type">String<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--></span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">)</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> (<span class="idris-bound">x</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">xs</span><!-- closing Bound False-->)
              -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-bound">contra</span><!-- closing Bound False--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">head</span><!-- closing Bound False--> <span class="idris-bound">tail</span><!-- closing Bound False-->) = <span class="idris-bound">contra</span><!-- closing Bound False--> <span class="idris-bound">head</span><!-- closing Bound False-->
</pre>


If the rest of the context has a free item then the context has not all been used.

<pre>
<span class="idris-function" title="
(ListD (String, Ty, Usage) ItemIsUsed xs ->
Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">tailIsAmerican</span><!-- closing Name Function "" "(ListD (String, Ty, Usage) ItemIsUsed xs ->\nVoid) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> : (<span class="idris-bound">contra</span><!-- closing Bound False--> : <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">(<span class="idris-type" title="Strings in some unspecified encoding
Type">String<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--></span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">)</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-bound">xs</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->)
              -&gt; <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">(<span class="idris-type" title="Strings in some unspecified encoding
Type">String<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--></span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">,</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">)</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--></span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> (<span class="idris-bound">x</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">xs</span><!-- closing Bound False-->)
              -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
<span class="idris-function" title="
(ListD (String, Ty, Usage) ItemIsUsed xs ->
Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">tailIsAmerican</span><!-- closing Name Function "" "(ListD (String, Ty, Usage) ItemIsUsed xs ->\nVoid) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-bound">contra</span><!-- closing Bound False--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">head</span><!-- closing Bound False--> <span class="idris-bound">tail</span><!-- closing Bound False-->) = <span class="idris-bound">contra</span><!-- closing Bound False--> <span class="idris-bound">tail</span><!-- closing Bound False-->
</pre>

Simply, a context has been used if all items have been used, otherwise there is too much freedom.

<pre>
<span class="idris-function" title="
(ctxt : Context) -> Dec (AllUsed ctxt)">allUsed</span><!-- closing Name Function "" "(ctxt : Context) -> Dec (AllUsed ctxt)"--> : (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->) -&gt; <span class="idris-type" title="Decidability. A decidable property either holds or
is a contradiction.
Type -> Type">Dec</span><!-- closing Name TypeConstructor "Decidability. A decidable property either holds or\nis a contradiction." "Type -> Type"--> (<span class="idris-function" title="
Context -> Type">AllUsed</span><!-- closing Name Function "" "Context -> Type"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
<span class="idris-function" title="
(ctxt : Context) -> Dec (AllUsed ctxt)">allUsed</span><!-- closing Name Function "" "(ctxt : Context) -> Dec (AllUsed ctxt)"--> <span class="idris-data" title="Empty list
List elem">[]</span><!-- closing Name Constructor "Empty list" "List elem"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-data" title="
ListD a e []">Empty</span><!-- closing Name Constructor "" "ListD a e []"-->
allUsed (x :: xs) <span class="idris-keyword"><span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsUsed x) ->
(xs : List (String, Ty, Usage)) ->
Dec (ListD (String, Ty, Usage)
           ItemIsUsed
           (x :: xs))"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-function" title="
(item : (String, Ty, Usage)) ->
Dec (ItemIsUsed item)">itemIsUsed</span><!-- closing Name Function "" "(item : (String, Ty, Usage)) ->\nDec (ItemIsUsed item)"--> <span class="idris-bound">x</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsUsed x) ->\n(xs : List (String, Ty, Usage)) ->\nDec (ListD (String, Ty, Usage)\n           ItemIsUsed\n           (x :: xs))"--></span><!-- closing Keyword-->
  allUsed (x :: xs) | (Yes prf) <span class="idris-keyword"><span class="idris-function" title="
(x : (String, Ty, Usage)) ->
ItemIsUsed x ->
(xs : List (String, Ty, Usage)) ->
Dec (ListD (String, Ty, Usage) ItemIsUsed xs) ->
Dec (ListD (String, Ty, Usage)
           ItemIsUsed
           (x :: xs))"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-function" title="
(ctxt : Context) -> Dec (AllUsed ctxt)">allUsed</span><!-- closing Name Function "" "(ctxt : Context) -> Dec (AllUsed ctxt)"--> <span class="idris-bound">xs</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nItemIsUsed x ->\n(xs : List (String, Ty, Usage)) ->\nDec (ListD (String, Ty, Usage) ItemIsUsed xs) ->\nDec (ListD (String, Ty, Usage)\n           ItemIsUsed\n           (x :: xs))"--></span><!-- closing Keyword-->
    <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
ItemIsUsed x ->
(xs : List (String, Ty, Usage)) ->
Dec (ListD (String, Ty, Usage) ItemIsUsed xs) ->
Dec (ListD (String, Ty, Usage)
           ItemIsUsed
           (x :: xs))">allUsed</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nItemIsUsed x ->\n(xs : List (String, Ty, Usage)) ->\nDec (ListD (String, Ty, Usage) ItemIsUsed xs) ->\nDec (ListD (String, Ty, Usage)\n           ItemIsUsed\n           (x :: xs))"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (Yes <span class="idris-bound">prf</span><!-- closing Bound False-->) | (<span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-bound">prfRest</span><!-- closing Bound False-->) = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">prf</span><!-- closing Bound False--> <span class="idris-bound">prfRest</span><!-- closing Bound False-->)
    <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
ItemIsUsed x ->
(xs : List (String, Ty, Usage)) ->
Dec (ListD (String, Ty, Usage) ItemIsUsed xs) ->
Dec (ListD (String, Ty, Usage)
           ItemIsUsed
           (x :: xs))">allUsed</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nItemIsUsed x ->\n(xs : List (String, Ty, Usage)) ->\nDec (ListD (String, Ty, Usage) ItemIsUsed xs) ->\nDec (ListD (String, Ty, Usage)\n           ItemIsUsed\n           (x :: xs))"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (Yes <span class="idris-bound">prf</span><!-- closing Bound False-->) | (<span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> <span class="idris-bound">contra</span><!-- closing Bound False-->) = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
(ListD (String, Ty, Usage) ItemIsUsed xs ->
Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">tailIsAmerican</span><!-- closing Name Function "" "(ListD (String, Ty, Usage) ItemIsUsed xs ->\nVoid) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-bound">contra</span><!-- closing Bound False-->)

  <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsUsed x) ->
(xs : List (String, Ty, Usage)) ->
Dec (ListD (String, Ty, Usage)
           ItemIsUsed
           (x :: xs))">allUsed</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsUsed x) ->\n(xs : List (String, Ty, Usage)) ->\nDec (ListD (String, Ty, Usage)\n           ItemIsUsed\n           (x :: xs))"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (<span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> <span class="idris-bound">contra</span><!-- closing Bound False-->) = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> ((<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-bound">contra</span><!-- closing Bound False-->))
</pre>

### The Real Problem

The real problem here is how can we construct an error message stating which elements in the context are free!

A really simple solution is to perform a value level computation to examine the context and report on the free entries.

However, we can do something a bit more interesting...

## Decidably Informative

The `Dec` data type is a powerful tool in dependently typed programming/proving to represent decidable information.
We have seen this with `allUsed`.

However a problem with `Dec` is that it is not informative in the negative case, only the positive.

We can prove the negative case, but not use that to construct error messages.
For instance, with entries are free in our context.

## Enter the DecInfo

`DecInfo` is variant of `Dec` to support construction of useful error messages for the negative case in a decidable procedure.
There is a copy of this in my containers library.

<pre>
<span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
descType -> trueType -> Type">DecInfo</span><!-- closing Name TypeConstructor "" "descType -> trueType -> Type"--> : (<span class="idris-bound">descWrong</span><!-- closing Bound False--> : <span class="idris-bound">descType</span><!-- closing Bound False-->)
            -&gt; (<span class="idris-bound">whyTrue</span><!-- closing Bound False-->   : <span class="idris-bound">trueType</span><!-- closing Bound False-->)
            -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
  <span class="idris-keyword">where</span><!-- closing Keyword-->
</pre>

Like `Dec` if we can prove something true then present evidence.

<pre>
    <span class="idris-data" title="
whyTrue -> DecInfo whyWrong whyTrue">Yes</span><!-- closing Name Constructor "" "whyTrue -> DecInfo whyWrong whyTrue"--> : (<span class="idris-bound">prf</span><!-- closing Bound False--> : <span class="idris-bound">whyTrue</span><!-- closing Bound False-->) -&gt; <span class="idris-type" title="
descType -> trueType -> Type">DecInfo</span><!-- closing Name TypeConstructor "" "descType -> trueType -> Type"--> <span class="idris-bound">whyWrong</span><!-- closing Bound False--> <span class="idris-bound">whyTrue</span><!-- closing Bound False-->
</pre>

If we can prove something false then allow us to provide something that helps describe why.

<pre>
    <span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"-->  : (<span class="idris-bound">desc</span><!-- closing Bound False--> : <span class="idris-bound">whyWrong</span><!-- closing Bound False-->)
       -&gt; (<span class="idris-bound">contra</span><!-- closing Bound False--> : <span class="idris-bound">whyTrue</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->)
       -&gt; <span class="idris-type" title="
descType -> trueType -> Type">DecInfo</span><!-- closing Name TypeConstructor "" "descType -> trueType -> Type"--> <span class="idris-bound">whyWrong</span><!-- closing Bound False--> <span class="idris-bound">whyTrue</span><!-- closing Bound False-->
</pre>

### An Example

We illustrate `DecInfo` with the following example:

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> DecInfoExample
</pre>


Record where in the context the error occurred and report the name of the free variable.

<pre>
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Type"><span class="idris-type" title="The type of types
Type">Desc</span><!-- closing Name TypeConstructor "The type of types" "Type"--></span><!-- closing Name TypeConstructor "" "Type"--> = <span class="idris-data" title="
String -> Desc">ErrHere</span><!-- closing Name Constructor "" "String -> Desc"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> | <span class="idris-data" title="
Desc -> Desc">ErrThere</span><!-- closing Name Constructor "" "Desc -> Desc"--> <span class="idris-type" title="
Type">Desc</span><!-- closing Name TypeConstructor "" "Type"-->
</pre>

Our new version of `allUsed'` is minimally modified, we add in the error reporting.

<pre>
  <span class="idris-function" title="
(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)">allUsed'</span><!-- closing Name Function "" "(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)"--> : (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->) -&gt; <span class="idris-type" title="
descType -> trueType -> Type">DecInfo</span><!-- closing Name TypeConstructor "" "descType -> trueType -> Type"--> <span class="idris-type" title="
Type">Desc</span><!-- closing Name TypeConstructor "" "Type"--> (<span class="idris-function" title="
Context -> Type">AllUsed</span><!-- closing Name Function "" "Context -> Type"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
  <span class="idris-function" title="
(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)">allUsed'</span><!-- closing Name Function "" "(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"--> = <span class="idris-data" title="
whyTrue -> DecInfo whyWrong whyTrue">Yes</span><!-- closing Name Constructor "" "whyTrue -> DecInfo whyWrong whyTrue"--> <span class="idris-data" title="
ListD a e []">Empty</span><!-- closing Name Constructor "" "ListD a e []"-->
  allUsed' (x :: xs) <span class="idris-keyword"><span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsUsed x) ->
(xs : List (String, Ty, Usage)) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               (x :: xs))"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-function" title="
(item : (String, Ty, Usage)) ->
Dec (ItemIsUsed item)">itemIsUsed</span><!-- closing Name Function "" "(item : (String, Ty, Usage)) ->\nDec (ItemIsUsed item)"--> <span class="idris-bound">x</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsUsed x) ->\n(xs : List (String, Ty, Usage)) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               (x :: xs))"--></span><!-- closing Keyword-->
    allUsed' (x :: xs) | (Yes prfHead) <span class="idris-keyword"><span class="idris-function" title="
(x : (String, Ty, Usage)) ->
ItemIsUsed x ->
(xs : List (String, Ty, Usage)) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               xs) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               (x :: xs))"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-function" title="
(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)">allUsed'</span><!-- closing Name Function "" "(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)"--> <span class="idris-bound">xs</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nItemIsUsed x ->\n(xs : List (String, Ty, Usage)) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               xs) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               (x :: xs))"--></span><!-- closing Keyword-->
      <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
ItemIsUsed x ->
(xs : List (String, Ty, Usage)) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               xs) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               (x :: xs))">allUsed'</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nItemIsUsed x ->\n(xs : List (String, Ty, Usage)) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               xs) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               (x :: xs))"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (Yes <span class="idris-bound">prfHead</span><!-- closing Bound False-->) | (<span class="idris-data" title="
whyTrue -> DecInfo whyWrong whyTrue">Yes</span><!-- closing Name Constructor "" "whyTrue -> DecInfo whyWrong whyTrue"--> <span class="idris-bound">prfTail</span><!-- closing Bound False-->) = <span class="idris-data" title="
whyTrue -> DecInfo whyWrong whyTrue">Yes</span><!-- closing Name Constructor "" "whyTrue -> DecInfo whyWrong whyTrue"--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">prfHead</span><!-- closing Bound False--> <span class="idris-bound">prfTail</span><!-- closing Bound False-->)
      <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
ItemIsUsed x ->
(xs : List (String, Ty, Usage)) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               xs) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               (x :: xs))">allUsed'</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nItemIsUsed x ->\n(xs : List (String, Ty, Usage)) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               xs) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               (x :: xs))"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (Yes <span class="idris-bound">prfHead</span><!-- closing Bound False-->) | (<span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"--> <span class="idris-bound">desc</span><!-- closing Bound False--> <span class="idris-bound">contra</span><!-- closing Bound False-->) = <span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"--> (<span class="idris-data" title="
Desc -> Desc">ErrThere</span><!-- closing Name Constructor "" "Desc -> Desc"--> <span class="idris-bound">desc</span><!-- closing Bound False-->) (<span class="idris-function" title="
(ListD (String, Ty, Usage) ItemIsUsed xs ->
Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">tailIsAmerican</span><!-- closing Name Function "" "(ListD (String, Ty, Usage) ItemIsUsed xs ->\nVoid) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-bound">contra</span><!-- closing Bound False-->)

    <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsUsed x) ->
(xs : List (String, Ty, Usage)) ->
DecInfo Desc
        (ListD (String, Ty, Usage)
               ItemIsUsed
               (x :: xs))">allUsed'</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsUsed x) ->\n(xs : List (String, Ty, Usage)) ->\nDecInfo Desc\n        (ListD (String, Ty, Usage)\n               ItemIsUsed\n               (x :: xs))"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (<span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> <span class="idris-bound">contra</span><!-- closing Bound False-->) = <span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"--> (<span class="idris-data" title="
String -> Desc">ErrHere</span><!-- closing Name Constructor "" "String -> Desc"--> (<span class="idris-function" title="Return the first element of a pair.
(a, b) -> a">fst</span><!-- closing Name Function "Return the first element of a pair." "(a, b) -> a"--> <span class="idris-bound">x</span><!-- closing Bound False-->)) (<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-bound">contra</span><!-- closing Bound False-->)
</pre>

#### Two examples:

Here we show some examples.

The first demonstrates `DecInfo` in action showing the result of calling `allUsed'` on a context with a free variable.

<pre>
  <span class="idris-function" title="
allUsed' [("a", A, Unrestricted),
          ("b", B, Free)] =
No (ErrThere (ErrHere "b"))
   (tailIsAmerican (headIsAmerican isAmerican))">example</span><!-- closing Name Function "" "allUsed' [(\"a\", A, Unrestricted),\n          (\"b\", B, Free)] =\nNo (ErrThere (ErrHere \"b\"))\n   (tailIsAmerican (headIsAmerican isAmerican))"--> : <span class="idris-function" title="
(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)">allUsed'</span><!-- closing Name Function "" "(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)"--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"a"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">A<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Unrestricted<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">,</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">B<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"--> (<span class="idris-data" title="
Desc -> Desc">ErrThere</span><!-- closing Name Constructor "" "Desc -> Desc"--> (<span class="idris-data" title="
String -> Desc">ErrHere</span><!-- closing Name Constructor "" "String -> Desc"--> <span class="idris-data" title="A string of length 1
String">"b"</span><!-- closing Name Constructor "A string of length 1" "String"-->))  (<span class="idris-function" title="
(ListD (String, Ty, Usage) ItemIsUsed xs ->
Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">tailIsAmerican</span><!-- closing Name Function "" "(ListD (String, Ty, Usage) ItemIsUsed xs ->\nVoid) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> (<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-function" title="
ItemIsUsed (label, ty, Free) -> Void">DecidablyUninformative.isAmerican</span><!-- closing Name Function "" "ItemIsUsed (label, ty, Free) -> Void"-->))
  <span class="idris-function" title="
allUsed' [("a", A, Unrestricted),
          ("b", B, Free)] =
No (ErrThere (ErrHere "b"))
   (tailIsAmerican (headIsAmerican isAmerican))">example</span><!-- closing Name Function "" "allUsed' [(\"a\", A, Unrestricted),\n          (\"b\", B, Free)] =\nNo (ErrThere (ErrHere \"b\"))\n   (tailIsAmerican (headIsAmerican isAmerican))"--> = <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
</pre>


Using this information, we can now use it to construct an error message containing the name of the free variable.

However, there is a problem.
Both `Dec` and `DecInfo` are greedy and will return at the first sign of trouble.

With two free variables in the context proof can only be constructed that the first element si free.

<pre>
  <span class="idris-function" title="
allUsed' [("a", A, Free), ("b", B, Free)] =
No (ErrHere "a") (headIsAmerican isAmerican)">example1</span><!-- closing Name Function "" "allUsed' [(\"a\", A, Free), (\"b\", B, Free)] =\nNo (ErrHere \"a\") (headIsAmerican isAmerican)"--> : <span class="idris-function" title="
(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)">allUsed'</span><!-- closing Name Function "" "(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)"-->  <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"a"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">A<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">,</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">B<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"--> (<span class="idris-data" title="
String -> Desc">ErrHere</span><!-- closing Name Constructor "" "String -> Desc"--> <span class="idris-data" title="A string of length 1
String">"a"</span><!-- closing Name Constructor "A string of length 1" "String"-->) (<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-function" title="
ItemIsUsed (label, ty, Free) -> Void">DecidablyUninformative.isAmerican</span><!-- closing Name Function "" "ItemIsUsed (label, ty, Free) -> Void"-->)
  <span class="idris-function" title="
allUsed' [("a", A, Free), ("b", B, Free)] =
No (ErrHere "a") (headIsAmerican isAmerican)">example1</span><!-- closing Name Function "" "allUsed' [(\"a\", A, Free), (\"b\", B, Free)] =\nNo (ErrHere \"a\") (headIsAmerican isAmerican)"--> = <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->

  <span class="idris-function" title="
allUsed' [("a", A, Free), ("b", B, Free)] =
No (ErrThere (ErrHere "b"))
   (tailIsAmerican (headIsAmerican isAmerican))">example1'</span><!-- closing Name Function "" "allUsed' [(\"a\", A, Free), (\"b\", B, Free)] =\nNo (ErrThere (ErrHere \"b\"))\n   (tailIsAmerican (headIsAmerican isAmerican))"--> : <span class="idris-function" title="
(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)">allUsed'</span><!-- closing Name Function "" "(ctxt : Context) -> DecInfo Desc (AllUsed ctxt)"-->  <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"a"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">A<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">,</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">B<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="
whyWrong ->
(whyTrue -> Void) -> DecInfo whyWrong whyTrue">No</span><!-- closing Name Constructor "" "whyWrong ->\n(whyTrue -> Void) -> DecInfo whyWrong whyTrue"--> (<span class="idris-data" title="
Desc -> Desc">ErrThere</span><!-- closing Name Constructor "" "Desc -> Desc"--> (<span class="idris-data" title="
String -> Desc">ErrHere</span><!-- closing Name Constructor "" "String -> Desc"--> <span class="idris-data" title="A string of length 1
String">"b"</span><!-- closing Name Constructor "A string of length 1" "String"-->)) (<span class="idris-function" title="
(ListD (String, Ty, Usage) ItemIsUsed xs ->
Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">tailIsAmerican</span><!-- closing Name Function "" "(ListD (String, Ty, Usage) ItemIsUsed xs ->\nVoid) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> (<span class="idris-function" title="
(ItemIsUsed x -> Void) ->
ListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->
Void">headIsAmerican</span><!-- closing Name Function "" "(ItemIsUsed x -> Void) ->\nListD (String, Ty, Usage) ItemIsUsed (x :: xs) ->\nVoid"--> <span class="idris-function" title="
ItemIsUsed (label, ty, Free) -> Void">DecidablyUninformative.isAmerican</span><!-- closing Name Function "" "ItemIsUsed (label, ty, Free) -> Void"-->))
  <span class="idris-function" title="
allUsed' [("a", A, Free), ("b", B, Free)] =
No (ErrThere (ErrHere "b"))
   (tailIsAmerican (headIsAmerican isAmerican))">example1'</span><!-- closing Name Function "" "allUsed' [(\"a\", A, Free), (\"b\", B, Free)] =\nNo (ErrThere (ErrHere \"b\"))\n   (tailIsAmerican (headIsAmerican isAmerican))"--> = ?rhs
</pre>

Expanding `?rhs` will fail to find a solution.

### Impact

The Impact here is that one will only discover each free variable in the context in turn as and when you fix the problems.
While this might be acceptable to some, to others it is not.
Surely we can report each an every free item in the context in a more formal way.

First we must recognise some freedom:

## Freedom

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> RecognisingFreedom

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> : (<span class="idris-bound">item</span><!-- closing Bound False--> : <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    <span class="idris-data" title="
(label : String) -> ItemIsFree (label, ty, Free)">IsFree</span><!-- closing Name Constructor "" "(label : String) -> ItemIsFree (label, ty, Free)"--> : (<span class="idris-bound">label</span><!-- closing Bound False--> : <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->) -&gt; <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">label<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">ty<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,<span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"-->

  <span class="idris-function" title="
ItemIsFree (label, ty, Consumed) -> Void">itemIsUsed'</span><!-- closing Name Function "" "ItemIsFree (label, ty, Consumed) -> Void"--> : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">label<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-bound">ty<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--> <span class="idris-data" title="
Usage">Consumed<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
  itemIsUsed' (IsFree _) <span class="idris-keyword">impossible</span><!-- closing Keyword-->

  <span class="idris-function" title="
ItemIsFree (label, ty, Unrestricted) -> Void">itemIsUnbound</span><!-- closing Name Function "" "ItemIsFree (label, ty, Unrestricted) -> Void"--> : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-bound">label<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-bound">ty<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Bound False--> <span class="idris-data" title="
Usage">Unrestricted<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->
  itemIsUnbound (IsFree _ ) <span class="idris-keyword">impossible</span><!-- closing Keyword-->

  <span class="idris-function" title="
(item : (String, Ty, Usage)) ->
Dec (ItemIsFree item)">itemIsFree</span><!-- closing Name Function "" "(item : (String, Ty, Usage)) ->\nDec (ItemIsFree item)"--> : (<span class="idris-bound">item</span><!-- closing Bound False--> : <span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) -&gt; <span class="idris-type" title="Decidability. A decidable property either holds or
is a contradiction.
Type -> Type">Dec</span><!-- closing Name TypeConstructor "Decidability. A decidable property either holds or\nis a contradiction." "Type -> Type"--> (<span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-bound">item</span><!-- closing Bound False-->)
  itemIsFree (label, (ty,use)) <span class="idris-keyword"><span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsFree (label, ty, warg))"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-bound">use</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsFree (label, ty, warg))"--></span><!-- closing Keyword-->
    <span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsFree (label, ty, warg))">itemIsFree</span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsFree (label, ty, warg))"--> (<span class="idris-bound">label</span><!-- closing Bound False-->, (<span class="idris-bound">ty</span><!-- closing Bound False-->,<span class="idris-bound">use</span><!-- closing Bound False-->)) | <span class="idris-data" title="
Usage">Consumed</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
ItemIsFree (label, ty, Consumed) -> Void">itemIsUsed'</span><!-- closing Name Function "" "ItemIsFree (label, ty, Consumed) -> Void"-->)
    <span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsFree (label, ty, warg))">itemIsFree</span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsFree (label, ty, warg))"--> (<span class="idris-bound">label</span><!-- closing Bound False-->, (<span class="idris-bound">ty</span><!-- closing Bound False-->,<span class="idris-bound">use</span><!-- closing Bound False-->)) | <span class="idris-data" title="
Usage">Free</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> (<span class="idris-data" title="
(label : String) -> ItemIsFree (label, ty, Free)">IsFree</span><!-- closing Name Constructor "" "(label : String) -> ItemIsFree (label, ty, Free)"--> <span class="idris-bound">label</span><!-- closing Bound False-->)
    <span class="idris-function" title="
(warg : Usage) ->
(label : String) ->
(ty : Ty) ->
Usage -> Dec (ItemIsFree (label, ty, warg))">itemIsFree</span><!-- closing Name Function "" "(warg : Usage) ->\n(label : String) ->\n(ty : Ty) ->\nUsage -> Dec (ItemIsFree (label, ty, warg))"--> (<span class="idris-bound">label</span><!-- closing Bound False-->, (<span class="idris-bound">ty</span><!-- closing Bound False-->,<span class="idris-bound">use</span><!-- closing Bound False-->)) | <span class="idris-data" title="
Usage">Unrestricted</span><!-- closing Name Constructor "" "Usage"--> = <span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> (<span class="idris-function" title="
ItemIsFree (label, ty, Unrestricted) -> Void">itemIsUnbound</span><!-- closing Name Function "" "ItemIsFree (label, ty, Unrestricted) -> Void"-->)
</pre>


## Separating the Wheat from the Chaff.

Order preserving encodings (thinnings) are a cool technique to keep account of items at the type-level.

In their simplest form we can use a thinning-like structure to show that items in our context will either be free or be used.
We show this as follows.

`ShowState` records if items in the context are free or not.
Here we have used a simple list structure, perhaps a better one will be a vector with an envariant that the length of `free`  and `used` is equal to the length of the context.

<pre>
<span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"--> : (<span class="idris-bound">free</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->)
              -&gt; (<span class="idris-bound">used</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->)
              -&gt; (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->)
              -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
  <span class="idris-keyword">where</span><!-- closing Keyword-->
</pre>

Empty  contexts are okay.

<pre>
    <span class="idris-data" title="
ShowState [] [] []">Empty</span><!-- closing Name Constructor "" "ShowState [] [] []"--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"-->
</pre>

If an item in our context is free, and we have proof of said freedom, then add the entry to the list of free entries.


<pre>
    <span class="idris-data" title="
ItemIsFree item ->
ShowState frees used ctxt ->
ShowState (item :: frees) used (item :: ctxt)">MovFree</span><!-- closing Name Constructor "" "ItemIsFree item ->\nShowState frees used ctxt ->\nShowState (item :: frees) used (item :: ctxt)"--> : (<span class="idris-bound">prf</span><!-- closing Bound False-->  : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"-->  <span class="idris-bound">item</span><!-- closing Bound False-->)
           -&gt; (<span class="idris-bound">rest</span><!-- closing Bound False--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->           <span class="idris-bound">frees</span><!-- closing Bound False-->  <span class="idris-bound">used</span><!-- closing Bound False-->          <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
           -&gt; <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->          (<span class="idris-bound">item</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">frees</span><!-- closing Bound False-->) <span class="idris-bound">used</span><!-- closing Bound False--> (<span class="idris-bound">item</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
</pre>

If an item in our context is not free, and we have proof of said usage, then add the entry to the list of used entries.

<pre>
    <span class="idris-data" title="
ItemIsUsed item ->
ShowState frees (item :: used) ctxt ->
ShowState frees used (item :: ctxt)">MovUsed</span><!-- closing Name Constructor "" "ItemIsUsed item ->\nShowState frees (item :: used) ctxt ->\nShowState frees used (item :: ctxt)"--> : (<span class="idris-bound">prf</span><!-- closing Bound False-->  : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsUsed</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"-->        <span class="idris-bound">item</span><!-- closing Bound False-->)
           -&gt; (<span class="idris-bound">rest</span><!-- closing Bound False--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->  <span class="idris-bound">frees</span><!-- closing Bound False--> (<span class="idris-bound">item<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Bound False--> <span class="idris-bound">used</span><!-- closing Bound False-->)          <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
           -&gt; <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->          <span class="idris-bound">frees</span><!-- closing Bound False-->         <span class="idris-bound">used</span><!-- closing Bound False-->  (<span class="idris-bound">item</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
</pre>

A problem with this approach is that we require distinct proofs to show freedom and usage.
When writing the corresponding function to construct this view then we do not have a way to show what to do in the negative case. That is, if something is not free then we must test if it is used if it si not used then we must test if it is free and if it is not free then we must test if it has been used ad infinitum.

A better approach would be to go back to our original statement about entry usage and forumlate our thinning as one that keeps proofs that an item is free, and proofs of void representing that an item has been used.

We use this formulation to allow us to preserve the 'positive proof' that something is used, and thus retain information required for error reporting.

Our `ShowState` now becomes:

<pre>
<span class="idris-keyword">namespace</span><!-- closing Keyword--> Better

  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"--> : (<span class="idris-bound">free</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->)
                 -&gt; (<span class="idris-bound">used</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->)
                 -&gt; (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->)
                 -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"-->
    <span class="idris-keyword">where</span><!-- closing Keyword-->
      <span class="idris-data" title="
ShowState' [] [] []">Empty</span><!-- closing Name Constructor "" "ShowState' [] [] []"--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"--> <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"-->

      <span class="idris-data" title="
(ItemIsFree item -> Void) ->
ShowState' frees used ctxt ->
ShowState' frees (item :: used) (item :: ctxt)">MovUsed</span><!-- closing Name Constructor "" "(ItemIsFree item -> Void) ->\nShowState' frees used ctxt ->\nShowState' frees (item :: used) (item :: ctxt)"--> : (<span class="idris-bound">prf</span><!-- closing Bound False-->  : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-bound">item</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="The empty type, also known as the trivially false
proposition.
Type">Void</span><!-- closing Name TypeConstructor "The empty type, also known as the trivially false\nproposition." "Type"-->)
             -&gt; (<span class="idris-bound">rest</span><!-- closing Bound False--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->     <span class="idris-bound">frees</span><!-- closing Bound False-->        <span class="idris-bound">used</span><!-- closing Bound False-->           <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
             -&gt; <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->             <span class="idris-bound">frees</span><!-- closing Bound False--> (<span class="idris-bound">item<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::<span class="idris-bound">used</span><!-- closing Bound False--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Bound False-->) (<span class="idris-bound">item</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)

      <span class="idris-data" title="
ItemIsFree item ->
ShowState' frees used ctxt ->
ShowState' (item :: frees) used (item :: ctxt)">MovFree</span><!-- closing Name Constructor "" "ItemIsFree item ->\nShowState' frees used ctxt ->\nShowState' (item :: frees) used (item :: ctxt)"--> : (<span class="idris-bound">prf</span><!-- closing Bound False-->  : <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"--> <span class="idris-bound">item</span><!-- closing Bound False-->)
             -&gt; (<span class="idris-bound">rest</span><!-- closing Bound False--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->               <span class="idris-bound">frees</span><!-- closing Bound False-->  <span class="idris-bound">used</span><!-- closing Bound False-->          <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
             -&gt; <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"-->              (<span class="idris-bound">item</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">frees</span><!-- closing Bound False-->) <span class="idris-bound">used</span><!-- closing Bound False--> (<span class="idris-bound">item</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
</pre>

We use a wrapper data type `TheState` to remove the need for dependent pairs and type-level quantification of free and used entries.
Further, `TheState` provides proof of the things that are free, and things that are used.

<pre>
  <span class="idris-keyword">data</span><!-- closing Keyword--> <span class="idris-type" title="
Context -> Type">TheState</span><!-- closing Name TypeConstructor "" "Context -> Type"--> : (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->) -&gt; <span class="idris-type" title="The type of types
Type">Type</span><!-- closing Name TypeConstructor "The type of types" "Type"--> <span class="idris-keyword">where</span><!-- closing Keyword-->
    <span class="idris-data" title="
ListD (String, Ty, Usage) ItemIsFree free ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
ShowState' free used ctxt -> TheState ctxt">MkSt</span><!-- closing Name Constructor "" "ListD (String, Ty, Usage) ItemIsFree free ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\nShowState' free used ctxt -> TheState ctxt"--> : (<span class="idris-bound">prfFree</span><!-- closing Bound False-->  : <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) (<span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"-->)       <span class="idris-bound">free</span><!-- closing Bound False-->)
        -&gt; (<span class="idris-bound">prfUsed</span><!-- closing Bound False-->  : <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) (<span class="idris-function" title="
Type -> Type">Not</span><!-- closing Name Function "" "Type -> Type"--> <span class="idris-function" title="Function composition
(b -> c) -> (a -> b) -> a -> c">.</span><!-- closing Name Function "Function composition" "(b -> c) -> (a -> b) -> a -> c"--> <span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"-->) <span class="idris-bound">used</span><!-- closing Bound False-->)
        -&gt; (<span class="idris-bound">theState</span><!-- closing Bound False--> : <span class="idris-type" title="
Context -> Context -> Context -> Type">ShowState'</span><!-- closing Name TypeConstructor "" "Context -> Context -> Context -> Type"--> <span class="idris-bound">free</span><!-- closing Bound False--> <span class="idris-bound">used</span><!-- closing Bound False--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)
        -&gt; <span class="idris-type" title="
Context -> Type">TheState</span><!-- closing Name TypeConstructor "" "Context -> Type"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->
</pre>

With `TheState` we can now construct a function to calculate the view and its proofs:

<pre>
  <span class="idris-function" title="
(ctxt : Context) -> TheState ctxt">calcState</span><!-- closing Name Function "" "(ctxt : Context) -> TheState ctxt"--> : (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->) -&gt; <span class="idris-type" title="
Context -> Type">TheState</span><!-- closing Name TypeConstructor "" "Context -> Type"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->
  <span class="idris-function" title="
(ctxt : Context) -> TheState ctxt">calcState</span><!-- closing Name Function "" "(ctxt : Context) -> TheState ctxt"--> <span class="idris-data" title="Empty list
List elem">[]</span><!-- closing Name Constructor "Empty list" "List elem"--> = <span class="idris-data" title="
ListD (String, Ty, Usage) ItemIsFree free ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
ShowState' free used ctxt -> TheState ctxt">MkSt</span><!-- closing Name Constructor "" "ListD (String, Ty, Usage) ItemIsFree free ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\nShowState' free used ctxt -> TheState ctxt"--> <span class="idris-data" title="
ListD a e []">Empty</span><!-- closing Name Constructor "" "ListD a e []"--> <span class="idris-data" title="
ListD a e []">Empty</span><!-- closing Name Constructor "" "ListD a e []"--> <span class="idris-data" title="
ShowState' [] [] []">Empty</span><!-- closing Name Constructor "" "ShowState' [] [] []"-->
  calcState (x :: xs) <span class="idris-keyword"><span class="idris-function" title="
(x : (String, Ty, Usage)) ->
(xs : List (String, Ty, Usage)) ->
TheState xs -> TheState (x :: xs)"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-function" title="
(ctxt : Context) -> TheState ctxt">calcState</span><!-- closing Name Function "" "(ctxt : Context) -> TheState ctxt"--> <span class="idris-bound">xs</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\n(xs : List (String, Ty, Usage)) ->\nTheState xs -> TheState (x :: xs)"--></span><!-- closing Keyword-->
    calcState (x :: xs) | (MkSt free used state) <span class="idris-keyword"><span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsFree x) ->
(xs : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (\x1 => ItemIsFree x1 -> Void)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used xs -> TheState (x :: xs)"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">with (<span class="idris-function" title="
(item : (String, Ty, Usage)) ->
Dec (ItemIsFree item)">itemIsFree</span><!-- closing Name Function "" "(item : (String, Ty, Usage)) ->\nDec (ItemIsFree item)"--> <span class="idris-bound">x</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsFree x) ->\n(xs : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (\\x1 => ItemIsFree x1 -> Void)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used xs -> TheState (x :: xs)"--></span><!-- closing Keyword-->
      <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsFree x) ->
(xs : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (\x1 => ItemIsFree x1 -> Void)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used xs -> TheState (x :: xs)">calcState</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsFree x) ->\n(xs : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (\\x1 => ItemIsFree x1 -> Void)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used xs -> TheState (x :: xs)"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (MkSt <span class="idris-bound">free</span><!-- closing Bound False--> <span class="idris-bound">used</span><!-- closing Bound False--> <span class="idris-bound">state</span><!-- closing Bound False-->) | (<span class="idris-data" title="The case where the property holds
prop -> Dec prop">Yes</span><!-- closing Name Constructor "The case where the property holds" "prop -> Dec prop"--> <span class="idris-bound">prf</span><!-- closing Bound False-->)   = <span class="idris-data" title="
ListD (String, Ty, Usage) ItemIsFree free ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
ShowState' free used ctxt -> TheState ctxt">MkSt</span><!-- closing Name Constructor "" "ListD (String, Ty, Usage) ItemIsFree free ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\nShowState' free used ctxt -> TheState ctxt"--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">prf</span><!-- closing Bound False--> <span class="idris-bound">free</span><!-- closing Bound False-->) <span class="idris-bound">used</span><!-- closing Bound False--> (<span class="idris-data" title="
ItemIsFree item ->
ShowState' frees used ctxt ->
ShowState' (item :: frees) used (item :: ctxt)">MovFree</span><!-- closing Name Constructor "" "ItemIsFree item ->\nShowState' frees used ctxt ->\nShowState' (item :: frees) used (item :: ctxt)"--> <span class="idris-bound">prf</span><!-- closing Bound False--> <span class="idris-bound">state</span><!-- closing Bound False-->)
      <span class="idris-function" title="
(x : (String, Ty, Usage)) ->
Dec (ItemIsFree x) ->
(xs : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (\x1 => ItemIsFree x1 -> Void)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used xs -> TheState (x :: xs)">calcState</span><!-- closing Name Function "" "(x : (String, Ty, Usage)) ->\nDec (ItemIsFree x) ->\n(xs : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (\\x1 => ItemIsFree x1 -> Void)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used xs -> TheState (x :: xs)"--> (<span class="idris-bound">x</span><!-- closing Bound False--> :: <span class="idris-bound">xs</span><!-- closing Bound False-->) | (MkSt <span class="idris-bound">free</span><!-- closing Bound False--> <span class="idris-bound">used</span><!-- closing Bound False--> <span class="idris-bound">state</span><!-- closing Bound False-->) | (<span class="idris-data" title="The case where the property holding would be a
contradiction
(prop -> Void) -> Dec prop">No</span><!-- closing Name Constructor "The case where the property holding would be a\ncontradiction" "(prop -> Void) -> Dec prop"--> <span class="idris-bound">contra</span><!-- closing Bound False-->) = <span class="idris-data" title="
ListD (String, Ty, Usage) ItemIsFree free ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
ShowState' free used ctxt -> TheState ctxt">MkSt</span><!-- closing Name Constructor "" "ListD (String, Ty, Usage) ItemIsFree free ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\nShowState' free used ctxt -> TheState ctxt"--> <span class="idris-bound">free</span><!-- closing Bound False--> (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> <span class="idris-bound">contra</span><!-- closing Bound False--> <span class="idris-bound">used</span><!-- closing Bound False-->) (<span class="idris-data" title="
(ItemIsFree item -> Void) ->
ShowState' frees used ctxt ->
ShowState' frees (item :: used) (item :: ctxt)">MovUsed</span><!-- closing Name Constructor "" "(ItemIsFree item -> Void) ->\nShowState' frees used ctxt ->\nShowState' frees (item :: used) (item :: ctxt)"--> <span class="idris-bound">contra</span><!-- closing Bound False--> <span class="idris-bound">state</span><!-- closing Bound False-->)
</pre>


and with this view use it to return a list of all names of free variables in our context.
When using this function in production we can examine the output to determine if there are unused variables, and if so which ones, together with the knowledge that how we do so is robust.

<pre>
  <span class="idris-function" title="
Context -> List String">isFree</span><!-- closing Name Function "" "Context -> List String"--> : (<span class="idris-bound">ctxt</span><!-- closing Bound False--> : <span class="idris-function" title="
Type">Context</span><!-- closing Name Function "" "Type"-->) -&gt; <span class="idris-type" title="Generic lists
Type -> Type">List</span><!-- closing Name TypeConstructor "Generic lists" "Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->
  isFree ctxt <span class="idris-keyword"><span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
TheState ctxt -> List String"><span class="idris-bound">with (<span class="idris-function" title="
(ctxt : Context) -> TheState ctxt">calcState</span><!-- closing Name Function "" "(ctxt : Context) -> TheState ctxt"--> <span class="idris-bound">ctxt</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\nTheState ctxt -> List String"--></span><!-- closing Keyword-->
    <span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
TheState ctxt -> List String">isFree</span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\nTheState ctxt -> List String"--> <span class="idris-bound">ctxt</span><!-- closing Bound False--> | (<span class="idris-data" title="
ListD (String, Ty, Usage) ItemIsFree free ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
ShowState' free used ctxt -> TheState ctxt">MkSt</span><!-- closing Name Constructor "" "ListD (String, Ty, Usage) ItemIsFree free ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\nShowState' free used ctxt -> TheState ctxt"--> <span class="idris-bound">free</span><!-- closing Bound False--> <span class="idris-bound">used</span><!-- closing Bound False--> <span class="idris-bound">state</span><!-- closing Bound False-->) = <span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used ctxt ->
ListD (String, Ty, Usage) ItemIsFree free' ->
List String"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">getNames <span class="idris-bound">free</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used ctxt ->\nListD (String, Ty, Usage) ItemIsFree free' ->\nList String"-->

      <span class="idris-keyword">where</span><!-- closing Keyword-->
        <span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used ctxt ->
ListD (String, Ty, Usage) ItemIsFree free' ->
List String">getNames</span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used ctxt ->\nListD (String, Ty, Usage) ItemIsFree free' ->\nList String"--> : <span class="idris-type" title="
(a : Type) -> (a -> Type) -> List a -> Type">ListD</span><!-- closing Name TypeConstructor "" "(a : Type) -> (a -> Type) -> List a -> Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"--> (<span class="idris-type" title="The non-dependent pair type, also known as
conjunction.
Type -> Type -> Type">Pair</span><!-- closing Name TypeConstructor "The non-dependent pair type, also known as\nconjunction." "Type -> Type -> Type"--> <span class="idris-type" title="
Type">Ty</span><!-- closing Name TypeConstructor "" "Type"--> <span class="idris-type" title="
Type">Usage</span><!-- closing Name TypeConstructor "" "Type"-->)) (<span class="idris-type" title="
(String, Ty, Usage) -> Type">ItemIsFree</span><!-- closing Name TypeConstructor "" "(String, Ty, Usage) -> Type"-->) <span class="idris-bound">free'</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="Generic lists
Type -> Type">List</span><!-- closing Name TypeConstructor "Generic lists" "Type -> Type"--> <span class="idris-type" title="Strings in some unspecified encoding
Type">String</span><!-- closing Name TypeConstructor "Strings in some unspecified encoding" "Type"-->
        <span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used ctxt ->
ListD (String, Ty, Usage) ItemIsFree free' ->
List String"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">getNames <span class="idris-data" title="
ListD a e []">Empty</span><!-- closing Name Constructor "" "ListD a e []"--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used ctxt ->\nListD (String, Ty, Usage) ItemIsFree free' ->\nList String"--> = <span class="idris-data" title="Empty list
List elem">Nil</span><!-- closing Name Constructor "Empty list" "List elem"-->
        <span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used ctxt ->
ListD (String, Ty, Usage) ItemIsFree free' ->
List String"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">getNames (<span class="idris-data" title="
e v -> ListD a e vs -> ListD a e (v :: vs)">Extend</span><!-- closing Name Constructor "" "e v -> ListD a e vs -> ListD a e (v :: vs)"--> (<span class="idris-data" title="
(label : String) -> ItemIsFree (label, ty, Free)">IsFree</span><!-- closing Name Constructor "" "(label : String) -> ItemIsFree (label, ty, Free)"--> <span class="idris-bound">label</span><!-- closing Bound False-->) <span class="idris-bound">tail</span><!-- closing Bound False-->)</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used ctxt ->\nListD (String, Ty, Usage) ItemIsFree free' ->\nList String"--> = <span class="idris-bound">label</span><!-- closing Bound False--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">::</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-function" title="
(ctxt : List (String, Ty, Usage)) ->
(used : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage)
      (Not . ItemIsFree)
      used ->
(free : List (String, Ty, Usage)) ->
ListD (String, Ty, Usage) ItemIsFree free ->
ShowState' free used ctxt ->
ListD (String, Ty, Usage) ItemIsFree free' ->
List String"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound"><span class="idris-bound">getNames <span class="idris-bound">tail</span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Bound False--></span><!-- closing Name Function "" "(ctxt : List (String, Ty, Usage)) ->\n(used : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage)\n      (Not . ItemIsFree)\n      used ->\n(free : List (String, Ty, Usage)) ->\nListD (String, Ty, Usage) ItemIsFree free ->\nShowState' free used ctxt ->\nListD (String, Ty, Usage) ItemIsFree free' ->\nList String"-->
</pre>

As an example here is a context from before showing `isFree` in action.

<pre>
  <span class="idris-function" title="
isFree [("a", A, Unrestricted), ("b", B, Free)] =
["b"]">example</span><!-- closing Name Function "" "isFree [(\"a\", A, Unrestricted), (\"b\", B, Free)] =\n[\"b\"]"--> : <span class="idris-function" title="
Context -> List String">isFree</span><!-- closing Name Function "" "Context -> List String"--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"a"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">A<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Unrestricted<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">,</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">B<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"-->
  <span class="idris-function" title="
isFree [("a", A, Unrestricted), ("b", B, Free)] =
["b"]">example</span><!-- closing Name Function "" "isFree [(\"a\", A, Unrestricted), (\"b\", B, Free)] =\n[\"b\"]"--> = <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->

  <span class="idris-function" title="
isFree [("a", A, Free), ("b", B, Free)] =
["a", "b"]">example1</span><!-- closing Name Function "" "isFree [(\"a\", A, Free), (\"b\", B, Free)] =\n[\"a\", \"b\"]"--> : <span class="idris-function" title="
Context -> List String">isFree</span><!-- closing Name Function "" "Context -> List String"--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"a"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">A<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">,</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="A pair of elements
A -> B -> (A, B)">(<span class="idris-data" title="
Ty">B<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">,</span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Ty"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--> <span class="idris-data" title="
Usage">Free<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="A pair of elements
A -> B -> (A, B)">)<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "A pair of elements" "A -> B -> (A, B)"--></span><!-- closing Name Constructor "" "Usage"--> <span class="idris-type" title="The propositional equality type. A proof that x =
y.
A -> B -> Type">=</span><!-- closing Name TypeConstructor "The propositional equality type. A proof that x =\ny." "A -> B -> Type"--> <span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">[<span class="idris-data" title="A string of length 1
String">"a"<span class="idris-data" title="A non-empty list, consisting of a head element and
the rest of the list.
elem -> List elem -> List elem">,</span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--></span><!-- closing Name Constructor "A string of length 1" "String"--></span><!-- closing Name Constructor "A non-empty list, consisting of a head element and\nthe rest of the list." "elem -> List elem -> List elem"--> <span class="idris-data" title="A string of length 1
String">"b"<span class="idris-data" title="Empty list
List elem">]</span><!-- closing Name Constructor "Empty list" "List elem"--></span><!-- closing Name Constructor "A string of length 1" "String"-->
  <span class="idris-function" title="
isFree [("a", A, Free), ("b", B, Free)] =
["a", "b"]">example1</span><!-- closing Name Function "" "isFree [(\"a\", A, Free), (\"b\", B, Free)] =\n[\"a\", \"b\"]"--> = <span class="idris-data" title="A proof that x in fact equals x. To construct
this, you must have already shown that both sides
are in fact equal.
x = x">Refl</span><!-- closing Name Constructor "A proof that x in fact equals x. To construct\nthis, you must have already shown that both sides\nare in fact equal." "x = x"-->
</pre>

## Coda

Programming with dependent types is cool and we can use those types to reason more precisely and informatively about our software programs.
When we do theorem proving our proofs do not 'fail' once they are written; they **are** proofs of correctness.

However, and especially when dealing with user input, we need the ability to be able to provide informative error messages in our software programs.
Decision procedures such as `Dec` and `DecInfo` are limited in what information they can present to construct error messages, and we need to think more carefully about how we use these tools in our code.

Hopefully, you may have learned something from this.

As a side note:
If we examine the structure of `TheState`, and its use in `calcState` and `isFree` we can see that if is essentially a 'verified' version of filter.

Compare with [this forumlation](https://github.com/jfdm/idris-containers/blob/master/Data/List/Filter.idr) that I borrowed from a Frenchman.
