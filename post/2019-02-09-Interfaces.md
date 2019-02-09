---
title:  Representing Interfaces when you have no Interfaces.
tags: idris,dependent-types,interfaces
...

I was chatting with someone about Interfaces/Type-classes and how in their language of choice you do not get default functions.
It reminded me of a little implementation trick I used in my thesis to *hot swap* model implementations in an evaluator I wrote.

I will show this trick using the dependently typed language Idris but make not that I don't see any real reason why this cannot be achieved in a language that supports polymorphism and indexed data types.

The core idea of this trick is to realise that within Idris Interfaces are realised as algebraic data types.

We can show this by approximating the `Num` interface with the following record:

<pre>
record MyNum (type : Type) where
  constructor MkNum
  add : type -> type -> type
  times : type -> type -> type
  fromInt : Integer -> type
</pre>

and an implementation that instantiates the fields with implementations for `Nat`

<pre>
<span class="idris-function" title="
MyNum Nat">natNum</span><!-- closing Name Function "" "MyNum Nat"--> : <span class="idris-type" title="
Type -> Type">MyNum</span><!-- closing Name TypeConstructor "" "Type -> Type"--> <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"-->
<span class="idris-function" title="
MyNum Nat">natNum</span><!-- closing Name Function "" "MyNum Nat"--> = <span class="idris-data" title="
(type -> type -> type) ->
(type -> type -> type) ->
(Integer -> type) -> MyNum type">MkNum</span><!-- closing Name Constructor "" "(type -> type -> type) ->\n(type -> type -> type) ->\n(Integer -> type) -> MyNum type"--> (<span class="idris-function" title="Add two natural numbers.
Nat -> Nat -> Nat">Nat.plus</span><!-- closing Name Function "Add two natural numbers." "Nat -> Nat -> Nat"-->) (<span class="idris-function" title="Multiply natural numbers
Nat -> Nat -> Nat">Nat.mult</span><!-- closing Name Function "Multiply natural numbers" "Nat -> Nat -> Nat"-->) (<span class="idris-function" title="Convert an Integer to a Nat, mapping negative
numbers to 0
Integer -> Nat">fromIntegerNat</span><!-- closing Name Function "Convert an Integer to a Nat, mapping negative\nnumbers to 0" "Integer -> Nat"-->)
</pre>

We can now start to write functions that use this 'interface', and where we would have an interface constraint we now explicitly pass around an implementation.

<pre>
<span class="idris-function" title="
MyNum type -> type -> type">double</span><!-- closing Name Function "" "MyNum type -> type -> type"--> : (<span class="idris-bound">impl</span><!-- closing Bound False--> : <span class="idris-type" title="
Type -> Type">MyNum</span><!-- closing Name TypeConstructor "" "Type -> Type"--> <span class="idris-bound">type</span><!-- closing Bound False-->) -&gt; (<span class="idris-bound">x</span><!-- closing Bound False--> : <span class="idris-bound">type</span><!-- closing Bound False-->) -&gt; <span class="idris-bound">type</span><!-- closing Bound False-->
<span class="idris-function" title="
MyNum type -> type -> type">double</span><!-- closing Name Function "" "MyNum type -> type -> type"--> <span class="idris-bound">impl</span><!-- closing Bound False--> <span class="idris-bound">x</span><!-- closing Bound False--> = (<span class="idris-function" title="
MyNum type -> type -> type -> type">add</span><!-- closing Name Function "" "MyNum type -> type -> type -> type"--> <span class="idris-bound">impl</span><!-- closing Bound False-->) <span class="idris-bound">x</span><!-- closing Bound False--> <span class="idris-bound">x</span><!-- closing Bound False-->
</pre>

Now with this setup we can also provide default functions.
Here is an approximation for the `Eq` interface:

<pre>
record MyEq (type : Type) where
  constructor MkEq
  equal : type -> type -> Bool
  notEqual : type -> type -> Bool
</pre>

We can construct factories to then build the default implementations for methods if they are provided.

<pre>
<span class="idris-function" title="
(type -> type -> Bool) ->
Maybe (type -> type -> Bool) -> MyEq type">mkEq</span><!-- closing Name Function "" "(type -> type -> Bool) ->\nMaybe (type -> type -> Bool) -> MyEq type"--> : (<span class="idris-bound">eq</span><!-- closing Bound False--> : <span class="idris-bound">type</span><!-- closing Bound False--> -&gt; <span class="idris-bound">type</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="Boolean Data Type
Type">Bool</span><!-- closing Name TypeConstructor "Boolean Data Type" "Type"-->)
    -&gt; (<span class="idris-bound">mNotEq</span><!-- closing Bound False--> : <span class="idris-type" title="An optional value. This can be used to represent
the possibility of failure, where a function may
return a value, or not.
Type -> Type">Maybe</span><!-- closing Name TypeConstructor "An optional value. This can be used to represent\nthe possibility of failure, where a function may\nreturn a value, or not." "Type -> Type"--> (<span class="idris-bound">type</span><!-- closing Bound False--> -&gt; <span class="idris-bound">type</span><!-- closing Bound False--> -&gt; <span class="idris-type" title="Boolean Data Type
Type">Bool</span><!-- closing Name TypeConstructor "Boolean Data Type" "Type"-->))
    -&gt; <span class="idris-type" title="
Type -> Type">MyEq</span><!-- closing Name TypeConstructor "" "Type -> Type"--> <span class="idris-bound">type</span><!-- closing Bound False-->
<span class="idris-function" title="
(type -> type -> Bool) ->
Maybe (type -> type -> Bool) -> MyEq type">mkEq</span><!-- closing Name Function "" "(type -> type -> Bool) ->\nMaybe (type -> type -> Bool) -> MyEq type"--> <span class="idris-bound">f</span><!-- closing Bound False--> <span class="idris-data" title="No value stored
Maybe a">Nothing</span><!-- closing Name Constructor "No value stored" "Maybe a"--> = <span class="idris-data" title="
(type -> type -> Bool) ->
(type -> type -> Bool) -> MyEq type">MkEq</span><!-- closing Name Constructor "" "(type -> type -> Bool) ->\n(type -> type -> Bool) -> MyEq type"--> <span class="idris-bound">f</span><!-- closing Bound False--> (\<span class="idris-bound">x</span><!-- closing Bound False-->, <span class="idris-bound">y</span><!-- closing Bound False--> =&gt; <span class="idris-function" title="Boolean NOT
Bool -> Bool">not</span><!-- closing Name Function "Boolean NOT" "Bool -> Bool"--> $ <span class="idris-bound">f</span><!-- closing Bound False--> <span class="idris-bound">x</span><!-- closing Bound False--> <span class="idris-bound">y</span><!-- closing Bound False-->)
<span class="idris-function" title="
(type -> type -> Bool) ->
Maybe (type -> type -> Bool) -> MyEq type">mkEq</span><!-- closing Name Function "" "(type -> type -> Bool) ->\nMaybe (type -> type -> Bool) -> MyEq type"--> <span class="idris-bound">f</span><!-- closing Bound False--> (<span class="idris-data" title="A value of type a is stored
a -> Maybe a">Just</span><!-- closing Name Constructor "A value of type a is stored" "a -> Maybe a"--> <span class="idris-bound">nf</span><!-- closing Bound False-->) = <span class="idris-data" title="
(type -> type -> Bool) ->
(type -> type -> Bool) -> MyEq type">MkEq</span><!-- closing Name Constructor "" "(type -> type -> Bool) ->\n(type -> type -> Bool) -> MyEq type"--> <span class="idris-bound">f</span><!-- closing Bound False--> <span class="idris-bound">nf</span><!-- closing Bound False-->
</pre>

Here we now construct an instance of `MyEq` for `Nats`.
First we define equality.

<pre>
<span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> : <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"--> -&gt; <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"--> -&gt; <span class="idris-type" title="Boolean Data Type
Type">Bool</span><!-- closing Name TypeConstructor "Boolean Data Type" "Type"-->
<span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> <span class="idris-data" title="Zero
Nat">Z</span><!-- closing Name Constructor "Zero" "Nat"-->     <span class="idris-data" title="Zero
Nat">Z</span><!-- closing Name Constructor "Zero" "Nat"-->     = <span class="idris-data" title="
Bool">True</span><!-- closing Name Constructor "" "Bool"-->
<span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">l</span><!-- closing Bound False-->) (<span class="idris-data" title="Successor
Nat -> Nat">S</span><!-- closing Name Constructor "Successor" "Nat -> Nat"--> <span class="idris-bound">r</span><!-- closing Bound False-->) = <span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> <span class="idris-bound">l</span><!-- closing Bound False--> <span class="idris-bound">r</span><!-- closing Bound False-->
<span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> _     _     = <span class="idris-data" title="
Bool">False</span><!-- closing Name Constructor "" "Bool"-->
</pre>

Then we can build an implementation that uses a 'default' implementation.

<pre>
<span class="idris-function" title="
MyEq Nat">natEq</span><!-- closing Name Function "" "MyEq Nat"--> : <span class="idris-type" title="
Type -> Type">MyEq</span><!-- closing Name TypeConstructor "" "Type -> Type"--> <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"-->
<span class="idris-function" title="
MyEq Nat">natEq</span><!-- closing Name Function "" "MyEq Nat"--> = <span class="idris-function" title="
(type -> type -> Bool) ->
Maybe (type -> type -> Bool) -> MyEq type">mkEq</span><!-- closing Name Function "" "(type -> type -> Bool) ->\nMaybe (type -> type -> Bool) -> MyEq type"--> <span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> <span class="idris-data" title="No value stored
Maybe a">Nothing</span><!-- closing Name Constructor "No value stored" "Maybe a"-->
</pre>

and one that does not.

<pre>
<span class="idris-function" title="
MyEq Nat">natEq'</span><!-- closing Name Function "" "MyEq Nat"--> : <span class="idris-type" title="
Type -> Type">MyEq</span><!-- closing Name TypeConstructor "" "Type -> Type"--> <span class="idris-type" title="Natural numbers: unbounded, unsigned integers
which can be pattern matched.
Type">Nat</span><!-- closing Name TypeConstructor "Natural numbers: unbounded, unsigned integers\nwhich can be pattern matched." "Type"-->
<span class="idris-function" title="
MyEq Nat">natEq'</span><!-- closing Name Function "" "MyEq Nat"--> = <span class="idris-function" title="
(type -> type -> Bool) ->
Maybe (type -> type -> Bool) -> MyEq type">mkEq</span><!-- closing Name Function "" "(type -> type -> Bool) ->\nMaybe (type -> type -> Bool) -> MyEq type"--> <span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> (<span class="idris-data" title="A value of type a is stored
a -> Maybe a">Just</span><!-- closing Name Constructor "A value of type a is stored" "a -> Maybe a"--> (\<span class="idris-bound">x</span><!-- closing Bound False-->,<span class="idris-bound">y</span><!-- closing Bound False--> =&gt; <span class="idris-function" title="Boolean NOT
Bool -> Bool">not</span><!-- closing Name Function "Boolean NOT" "Bool -> Bool"--> $ <span class="idris-function" title="
Nat -> Nat -> Bool">natEqFunc</span><!-- closing Name Function "" "Nat -> Nat -> Bool"--> <span class="idris-bound">x</span><!-- closing Bound False--> <span class="idris-bound">y</span><!-- closing Bound False-->))
</pre>

As a final thought, what about implementing default implementations in terms of the 'interface' itself.
For that I would suggest removing those functions as fields and write functions that use the 'interface'.

PS

The reason records are not highlighted nicely is due to issues with Idris' highlighting code for records.
