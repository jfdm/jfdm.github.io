---
title: Programming with Holes
tags: idris,dependent-types,tdd,musing
...

Traditionally, computer programs must be complete when presented to the compiler.
Typed Holes (also known as meta variables) are an important tool when programming that supports computing with incomplete programs in which holes (the things we do not know) are a core aspect of the language (and tooling) design.
Specifically, if you have used dependently typed languages such as Idris and Agda you will have encountered holes before.
Typed Holes in Idris allow us to inspect the local typing context from where the hole was placed.
This allows us to see what information is directly available when looking to fill the hole.
Further, computing the type of the typed hole also tells us the type of thing we need to insert.

For example, take the following simple incomplete function:

```idris
hole_example : (input : Bool) -> Bool
hole_example input = ?rhs && input
```

Here the hole is signified using `?rhs` and tells the compiler that we don't know what should go here.
Asking the compiler the type of `?rhs` tells us what is available, and that `?rhs` expects a boolean expression.

```idris
Hole> :t Hole.rhs
   input : Bool
----------------------------------
   rhs : Bool
```

So the question is how to incorporate the notion of typed holes in a language.
I am interested in adding typed-holes to the DSLs I develop as part of my work.
Once I get other things finished, I think typed holes are a good feature to have to help user's learn the language.
So, as part of my studies I decided to explore how to build a simply-typed expression language with holes and construct a type-checker to work with them.

We will be doing this in Idris, and let's see what we can do.

## Our Razor

We will use the following simply typed expression language that supports:
boolean conjunction;
natural number addition; and
binding expressions to names.

Our types are simply Booleans and Natural numbers:

```idris
data Ty = BOOL | NAT
```

and expressions support values, conjunction, addition, binding and references:

```idris
data Expr = B Bool | N Nat
          | AndB Expr Expr
          | AddN Expr Expr
          | Let String Expr Ty Expr
          | Ref String
          | Hole String
```

Notice that alongside our expected constructs there is `Hole` our expression that represents a 'typed hole'.
Now this hole is not typed and we will see in our type checker have we can discover the hole's type.

To make the presentation simple, I have used string-based naming and we will use extrinsic type checking.
A good exercise will be to use DeBruijn indices, combined with intrinsically (well-typed) expressions, to ensure names are unique (based on their order of definition) and expressions are well-typed.

## Type Checker

Within Idris, typed holes really come into their own when type-checking expressions.
Thus, our type checker needs to be able to return a local typing context with the locally bound variables as well as the usual True if things are well-typed.

We will now look at building a type checker.

### Errors

Type-checking errors will consist of type mismatches and unbound names.

```idris
data Error = MM Ty Ty | NotAvar String
```

### Results

Successful type-checking of a complete expression will return a type---`T`.
Successful type-checking of an incomplete expression will (greedily) return `H` which includes the name of the first hole encountered, its type, and the local typing context.
A more involved result will be to return a list of wholes encountered.

An important aspect with typed holes is that of type-inference, we need to know the hole's type.
Given that we are in a simply typed expression language we can cheat and include an intermediate result (`HuTy`) that tells us we have encountered a hole and it needs to be typed.
For more involved languages such type-inference is important and would require extra steps.
A good exercise will be to see what happens when using well-typed expressions!


```
data Res = T Ty
         | H String Ty (List (String, Ty))
         | HuTy String
```

### The Checker

We are now ready to write our type checker that, given a typing context and an expression, will either return an error or a result.

```idris
check : (ctxt : List (String, Ty))
     -> (expr : Expr)
     -> Either Error Res
```

#### Constants

Type checking constants are straightforward:

```idris
check ctxt (B x) = Right (T BOOL)
check ctxt (N k) = Right (T NAT)
```

#### Binary Operations

Type checking the two binary operations (conjunction and addition) are identical.
First we check the left operand and then the right operand.
If both operands are the same type we return that type, and ill-typed terms return a type mismatch error.
If we encounter an untyped hole we can then assert its type and return the local context.
Otherwise we propagate the hole as the type-checking result.

```idris
check ctxt (AndB x y)
  = do T BOOL <- check ctxt x
                  | T ty   => Left (MM BOOL ty)
                  | HuTy s => pure (H s BOOL ctxt)
                  | x      => pure x
       T BOOL <- check ctxt y
                  | T ty   => Left (MM BOOL ty)
                  | HuTy s => pure (H s BOOL ctxt)
                  | x      => pure x

       pure (T BOOL)

check ctxt (AddN x y)
  = do T NAT <- check ctxt x
                 | T ty   => Left (MM NAT ty)
                 | HuTy s => pure (H s NAT ctxt)
                 | x      => pure x
       T NAT <- check ctxt y
                 | T ty   => Left (MM NAT ty)
                 | HuTy s => pure (H s NAT ctxt)
                 | x      => pure x
       pure (T NAT)
```

#### Let-Bindings

We take similar actions with Let-bindings as we did with our binary operations.
Encountering an untyped hole as the bound expression requires us to assert the expression's type, otherwise we propagate a found hole as the result.
If the bound expression does not match its ascription then a type-mismatch is returned.
Otherwise we check the body with an expanded context.

```idris
check ctxt (Let n e ty b)
  = do T tyE <- check ctxt e
                  | HuTy s => pure (H s ty ctxt)
                  | x      => pure x
       if ty == tyE
         then check ((n,ty)::ctxt) b
         else Left (MM ty tyE)
```

#### References

References lookup the name in the typing context and return the found type, otherwise the case raises an error.


```idris
check ctxt (Ref x)
  = case (lookup x ctxt) of
      Nothing => Left (NotAvar x)
      Just ty => Right (T ty)
```

We assume that we have presented an instance of `Eq` for `Ty` so that `lookup` works.

#### Holes

When encountering a hole we return the untyped hole.

```idris
check ctxt (Hole x) = pure (HuTy x)
```

### Running the Checker

We finish the type-checker with a simple function that runs the check with an empty context.

```idris
runCheck : (expr : Expr) -> Either Error Res
runCheck = check Nil
```

## Examples

We end with some examples:


```idris
test : Expr
test = Let "x" (B False) BOOL (AndB (B False) (Hole "?this"))
```

results in:

```
Hole> runCheck test
Right (H "?this" BOOL [("x", BOOL)])
```

and:

```idris
test1 : Expr
test1 = (AndB (B False) (Hole "?this"))
```

results in:

```
Hole> runCheck test1
Right (H "?this" BOOL [])
```

and:

```idris
test2 : Expr
test2 = (AndB (B False) (N 1))
```

results in:

```
Hole> runCheck test2
Left (MM BOOL NAT)
```

and:

```idris
test3 : Expr
test3 = (AndB (Hole "?this") (N 1))
```

results in:

```
Hole> runCheck test3
Right (H "?this" BOOL [])
```

All of which are expected.
Well-typed complete programs return the program's type.
Ill-typed complete program's fail, and
Ill-typed incomplete programmes will return a hole if the hole is found before ill-typed expression.
Our type-checking traverses the expressions left-to-right, and fails early.

## Coda

This was a simple exercise in trying to realise a simple language with typed holes.
Typed Holes are not limited to Idris and Agda, and how these languages work underneath in dealing with holes is more involved.
These languages are more involved, especially if we look at Idris2 construction in which names (even those for) holes are well-scoped, and for these language's type-checking doesn't just return a yes or no but returns something more.

As a side note, I learned a few years ago that Haskell also supports typed holes, and are represented by an underscore (`_`) that is placed on the right-hand side of an equation.
When I get back to teaching Haskell (or really Idris2) holes will be an important feature to consider.

More importantly there is some interesting research in providing principled approaches to typed-hole driven development in [Hazel](https://hazel.org/) a live functional programming language environment with typed-holes.
You should look at Hazel and what the research team behind it's development are up to.
