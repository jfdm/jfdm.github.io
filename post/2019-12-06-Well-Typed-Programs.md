---
title: Well-Typed Expressions lead to Well-Typed Well-Scoped Programs
tags: idris,dependent-types,tdd,musing
...

Let us consider the /Well-Typed Interpreter/ (WTI), a well known application of dependent types to ensure that our program's are not only well-typed but also well-scoped w.r.t. variables.
To be specific the WTI details not how program's are correct but /expressions/.
When dealing with program's we will have a top-level expression that *may* depend on globally declared expressions.

In this post I will describe a Razor, detailing how with a little thought we can use the concept of the WTI to described /Well-Typed Programs/.

Further, I will also show how we can then convert a well-typed expression language to a well-typed program where certain Let-bound expressions are promoted to declarations.
Thus, showing in some ways how to use dependent types for well-typed program transformations.

This post was derived from a literate Idris file so there will be some cruft related to Idris.

    module Main

We will need some data structures, and helper functions, not defined in Idris' prelude.

    import Data.List

The following import is from my [container's library](https://github.com/jfdm/idris-containers), we will need these in the final sections to keep our musing's DRY.

    import Data.DList

Totality is a good thing here.

    %default total

## A Well-Typed Expression Language.

    namespace Source

Here we shall describe a well-typed expression language based on Hutton's Original Razor.

### Types

Within our expression language our types are either Boolean's or Integers:

      data Ty = BOOL | INT

### Expressions

Using dependent types we can then construct our expression language as an algebraic data type whose type is indexed by the type of expressions:

      data Expr : Ty -> Type where

We now describe our language's expressions:

        Ref : String -> (ty : Ty) -> Expr ty

Our references are not well-scoped using DeBruijn indicies.
I have done this purposefully to mirror a problem in a code generation tool I am currently developing.

        I : Int -> Expr INT
        B : Bool -> Expr BOOL

Our values contain values.
I have simplified values specification and an alternative formulation would be to specify a singular constructor with a type-level function to calculate the type of the value from an instance of `Ty`.
This is not required for this post.

        Add : Expr INT -> Expr INT -> Expr INT
        And : Expr BOOL -> Expr BOOL -> Expr BOOL

For each of our base types we present a singular binary operation (conjunction for booleans, and addition for integers).

        Let : (binder : String) -> Expr typeA -> Expr typeB -> Expr typeB

Standard Let-bindings introduce variables.

### Examples

Here we describe some instances of our expression language.

     example0 : Expr BOOL
     example0 = And (B False) (B True)

     example1 : Expr INT
     example1 = Add (I 5) (I 9)

     example2 : Expr BOOL
     example2 = Let "x" example0
                    (And (Ref "x" BOOL) example0)

     example3 : Expr INT
     example3 = Let "x" example1
                    (Add (Ref "x" INT) example1)

     example4 : Expr INT
     example4 = Let "y" example0
                    (Let "z" (Ref "y" BOOL)
                         (Add (I 4) example3)
                    )

     example : Expr INT
     example = Let "x" example0
                   (Let "y" example1
                        (Let "z" (I 6)
                             (Let "a" (And (B False) (Ref "x" BOOL))
                                  (Add (Ref "z" INT) (Ref "y" INT))
                             )
                        )
                   )

## A Well-Typed Well-Scoped Program

    namespace Destination

Here we describe our well-typed and well scoped program.
Many of the construct's used follow that from the WTI and may be familiar, if not my previous post on [Hutton's Razor(s)](#) should give a quick introduction.

### Types

Like our expression language we have two types: Booleans and Integers.

       data Ty = INT | BOOL

### Context

We can use our types to define a typing context as a list of name-value pairs.

       Context : Type
       Context = List (String, Destination.Ty)

To help us construct existenial proofs (DeBruijn indicies) that a name-type pairing exisits in the typing context we need to provide an instance of Decidable Equality.

       intNotBool : Destination.INT = Destination.BOOL -     Void
       intNotBool Refl impossible

       DecEq Destination.Ty where
         decEq INT INT = Yes Refl
         decEq INT BOOL = No intNotBool
         decEq BOOL INT = No (negEqSym intNotBool)
         decEq BOOL BOOL = Yes Refl

Fortunatly, our language has two types or we would be here for a while providing a coherent proof of decidable equality...

### Expressions

We now go on to describe our expression language.

       data Expr : (local  : Context)
                -> (global : Context)
                -> (type : Destination.Ty)
                -> Type
         where

Our trick to describing well-typed programs is to parameterise the type of our expressions with *two* contexts: a local context; and global context.

           Local  : Elem (binder, ty) local  -> Expr local global ty
           Global : Elem (binder, ty) global -> Expr local global ty

We can now define two kinds of references a `Local` reference that refers to a locally bound expression, and a `Global` reference that refers to a globally bound expression.

           I : Int  -> Expr local global INT
           B : Bool -> Expr local global BOOL

As before, values are values.

           And : Expr local global BOOL
              -> Expr local global BOOL
              -> Expr local global BOOL

           Add : Expr local global INT
              -> Expr local global INT
              -> Expr local global INT

And our two operations are defined as before.

           Let : (this   : String)
              -> (beThis : Expr local global x)
              -> (inThis : Expr ((binder,x)::local) global y)
              -> Expr local global y

`Let` is a binding site to bind an expression to a variable name.
As our well-scoped terms rely on true names, our let binding also requires that we provide the binder and at the type-level we extend the context for `inThis` with the introduced variable name.

#### Examples

We now give some simple examples using locally and globaly bound expressions.

       expr : Expr Nil Nil BOOL
       expr = (Let "x" (B True)
                   (And (Local Here) (B False)))

       expr1 : Expr Nil [("foo", INT)] INT
       expr1 = (Let "x" (I 1)
                    (Add (Local Here) (Global Here)))
### Declarations

Our attention now turns to global declarations.
We define this using a cons-style list that contains expressions bound to names.

       data Decls : (global : Context) -> Type where

We index the type of delcarations with the global context ensuring that our declarations can refer to earlier defined declarations.

         Empty   : Decls Nil

It is okay to have no global declarations in our programs.

         DeclAdd : (binder : String)
                -> (expr   : Expr Nil global type)
                -> (rest   : Decls global)
                -> Decls ((MkPair binder type) :: global)

`DeclAdd` allows us to extend our list of declarations.
We require that our expressions are *closed terms* w.r.t to the local context.
Addition of a declaration extends the global context by one.

Our declarations mirror `Let` bindings from our expressions.

**Note** that our use of real names makes our well-scoped representations named rather than *nameless*.
We still need to think how to ensure that our list contains unique names in a nice fashion.

### Programs

We have expressions and declarations, so let us now define a program as a set of declarations paired with a single closed term.

       data Prog : Type where
         MkProg : Decls global
               -> Expr Nil global type
               -> Prog

Done!

And here is an example program:

       prog : Prog
       prog = MkProg (DeclAdd "bar" (Let "x" (B True) (And (Local Here) (B False)))
                              (DeclAdd "foo" (I 2) Empty))
                     (Let "x" (I 1)
                          (Add (Local Here) (Global (There Here))))

## Going from Source to Destination.

We have thus far shown an expression language, and a /program language/.
Let us now consider how to build a program from an expression.

### Type interpretation

We first describe a function `interpTy` to map types from our expression language to our program language.

       interpTy : Source.Ty -> Destination.Ty
       interpTy BOOL = BOOL
       interpTy INT  = INT

### Build Environment

As with interpretation in the WTI we will have a /build environment/ to keep track of our local typing context and store our global declarations.

       data BuildEnv : (genv, lenv : Context)
                    -> Type
         where
           MkBEnv : (decls  : Decls global)
                 -> (local  : Context)
                 -> BuildEnv global local

### Build Result

We also need a build result to return the resulting top-level expression and list of declarations that the expression depends upon.

       data BuildRes : (genv, lenv : Context)
                    -> Destination.Ty
                    -> Type
         where
           MkBRes : Decls genv
                 -> Expr lenv genv type
                 -> BuildRes genv lenv type

We also provide a default environment.

       defaultEnv : BuildEnv Nil Nil
       defaultEnv = MkBEnv Empty Nil

### Build Errors

Unfortunately, our conversion between the two programs will not be perfect and errors can happen.
We present a set of helpful errors to help describe problems we have.

       data Error = NotAVar String

                  | AddLOperandWrong Error
                  | AddROperandWrong Error

                  | AndLOperandWrong Error
                  | AndROperandWrong Error

                  | BadContextL String (Context) Context
                  | BadContextV (Context) Context

                  | ToGlobalErrorExpr String Error
                  | ToGlobalErrorBody Error

                  | ToLocalErrorExpr String Error
                  | ToLocalErrorBody Error

### Nasty Hack

When we convert the `inThis` body of a let binding for local variables we may extend the global context with new declarations.
We need `updateThis` to facilitate updating the global references in the `this` expression.


       updateThis : (globalY : Context)
          -> (this    : Expr local globalX type)
          -> Either Error (Expr local globalY type)
       updateThis globalY (And x y) =
         do x' <- (updateThis globalY x)
            y' <- (updateThis globalY y)
            pure $ And x' y'
       updateThis globalY (Add x y) =
         do x' <- (updateThis globalY x)
            y' <- (updateThis globalY y)
            pure $ Add x' y'
       updateThis globalY (Let binder y z) =
         do x' <- (updateThis globalY y)
            y' <- (updateThis globalY z)
            pure $ Let binder x' y'

       updateThis globalY (Global {binder} {ty} x) with (isElem (binder,ty) globalY)
         updateThis globalY (Global {binder = binder} {ty = ty} x) | (Yes prf) = pure $ Global prf
         updateThis globalY (Global {binder = binder} {ty = ty} x) | (No contra) = Left $ NotAVar binder

       updateThis globalY (Local x) = pure $ Local x
       updateThis globalY (I x) = pure $ I x
       updateThis globalY (B x) = pure $ B x


There will probably be a better way to do this, as described in PLFA, but this is a quick and cheap hack...

### The Conversion function!

With all our machinery we can now construct our conversion function:

       convert : (env : BuildEnv global lenv)
              -> (expr : Source.Expr type)
              -> Either Error (genv' ** BuildRes genv' lenv (interpTy type))

The result of converting an expression `expr`, with assumed environment `env`, will either be an error or the converted expression together with the global declarations.
For *this* conversion we will promote all Boolean typed variables to be global declarations.

For conversion to work properly we assume that our expression language is in a normal form: all let-bindings have been floated to the top of the expression tree.

       convert (MkBEnv {global} decls lenv) (Ref x type) with (interpTy type)
         convert (MkBEnv {global} decls lenv) (Ref x type) | ty with (isElem (x,ty) lenv)
           convert (MkBEnv {global} decls lenv) (Ref x type) | ty | (Yes prf) =
               pure (_ ** MkBRes decls (Local prf))
           convert (MkBEnv {global} decls lenv) (Ref x type) | ty | (No contra) with (isElem (x,ty) global)
             convert (MkBEnv {global = global} decls lenv) (Ref x type) | ty | (No contra) | (Yes prf) =
               pure (_ ** MkBRes decls (Global prf))
             convert (MkBEnv {global = global} decls lenv) (Ref x type) | ty | (No contra) | (No f) = Left (NotAVar x)

When encountering a reference from the expression language, we check if the reference refers to a global or local context.
If it doesn't then we have an error.

       convert env@(MkBEnv ds lenv) (I x) = pure $ (_ ** MkBRes ds (I x))
       convert env@(MkBEnv ds lenv) (B x) = pure $ (_ ** MkBRes ds (B x))

Constant conversion is straightforward.

Conversion of operations is that liitle bit more involved both require that we convert both operands, however we need to ensure that the resulting global contexts are the same.
If not then an error has occurred.

**Note** Some of this code will be hard to read as we have to use dependent pattern matching when using dependent pairs.
I think this can be simpilified to using Do-notation and considered use of `case` but this works...

       convert env (Add x y) with (convert env x)
         convert env (Add x y) | Left err = Left (AddLOperandWrong err)
         convert env (Add x y) | (Right z) with (z)
           convert env (Add x y) | (Right z) | (g' ** pfX) with (pfX)
             convert env (Add x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') with (convert env y)
               convert env (Add x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | Left err = Left (AddROperandWrong err)
               convert env (Add x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) with (w)
                 convert env (Add x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) with (pfY)
                   convert env (Add x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) | (MkBRes declsY y') with (decEq g' g'')
                     convert env (Add x y) | (Right z) | (g'' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) | (MkBRes declsY y') | (Yes Refl) = pure (_ ** MkBRes declsY (Add x' y'))
                     convert env (Add x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) | (MkBRes declsY y') | (No contra) = Left (BadContextV g' g'')

More of the same!

       convert env (And x y) with (convert env x)
         convert env (And x y) | Left err = Left (AndLOperandWrong err)
         convert env (And x y) | (Right z) with (z)
           convert env (And x y) | (Right z) | (g' ** pfX) with (pfX)
             convert env (And x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') with (convert env y)
               convert env (And x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | Left err = Left (AndROperandWrong err)
               convert env (And x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) with (w)
                 convert env (And x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) with (pfY)
                   convert env (And x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) | (MkBRes declsY y') with (decEq g' g'')
                     convert env (And x y) | (Right z) | (g'' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) | (MkBRes declsY y') | (Yes Refl) = pure (_ ** MkBRes declsY (And x' y'))
                     convert env (And x y) | (Right z) | (g' ** pfX) | (MkBRes declsX x') | (Right w) | (g'' ** pfY) | (MkBRes declsY y') | (No contra) = Left (BadContextV g' g'')


We now move onto dealing with let bindings.
If the variable has type boolean then we promote it to a global definition.

       convert env (Let binder x {typeA} y) with (typeA)

First we convert the expression to be bound, ensuring that it is closed.

         convert (MkBEnv ds lenv) (Let binder x {typeA = typeA} y) | BOOL with (convert (MkBEnv ds Nil) x)
           convert (MkBEnv ds lenv) (Let binder x {typeA = typeA} y) | BOOL | Left err = Left (ToGlobalErrorExpr binder err)
           convert (MkBEnv ds lenv) (Let binder x {typeA = typeA} y) | BOOL | (Right resX) with (resX)
             convert (MkBEnv ds lenv) (Let binder x {typeA = typeA} y) | BOOL | (Right resX) | (globalX ** exprX) with (exprX)

Then we extend our list of global declarations and return the result of converting the body.

               convert (MkBEnv ds lenv) (Let binder x {typeA = typeA} y) | BOOL | (Right resX) | (globalX ** exprX) | (MkBRes declsX x') = convert (MkBEnv (DeclAdd binder x' declsX) lenv) y

Now to look at converting locally bound variables, which we do not assume are closed.

         convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT with (convert (MkBEnv decls lenv) x)
           convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Left l) = Left (ToLocalErrorExpr binder l)
           convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) with (resX)
             convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) | (globalX ** exprX) with (exprX)

Once we have converted the expression to be bound we can look at converting the body.

               convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) | (globalX ** exprX) | (MkBRes declsX x') with (convert (MkBEnv decls ((binder,INT)::lenv)) y)
                 convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) | (globalX ** exprX) | (MkBRes declsX x') | (Left l) = Left (ToLocalErrorBody l)
                 convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) | (globalX ** exprX) | (MkBRes declsX x') | (Right resY) with (resY)
                   convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) | (globalX ** exprX) | (MkBRes declsX x') | (Right resY) | (globalY ** exprY) with (exprY)
                     convert (MkBEnv decls lenv) (Let binder x {typeA = typeA} y) | INT | (Right resX) | (globalX ** exprX) | (MkBRes declsX x') | (Right resY) | (globalY ** exprY) | (MkBRes declsY y') =

Remember we need to update the variable's value with the new set of global declarations.

                       do x'' <- updateThis globalY x'

Now we can return the new `Let` binding.

                          pure (_ ** MkBRes declsY (Let binder x'' y'))

#### Helper functions

To make like easier we define `convert'`, a helper function to set up the default environment for conversion.

       convert' : (expr : Source.Expr type)
                 -> Either Error (genv ** BuildRes genv Nil (interpTy type))
       convert' expr = convert defaultEnv expr

and `runConvert` to construct a program instance:

       runConvert : (expr : Source.Expr type)
                 -> Either Error Prog
       runConvert expr =
         case convert' expr of
           Left err =     Left err
           Right (_ ** MkBRes decls e') =     Right (MkProg decls e')


## Example

We end with an example:

Here is an example expression we defined earlier:

```
λΠ> Source.example
Let "x"
    (And (B False) (B True))
    (Let "y"
         (Add (I 5) (I 9))
         (Let "z"
              (I 6)
              (Let "a"
                   (And (B False) (Ref "x" BOOL))
                   (Add (Ref "z" INT) (Ref "y" INT))))) : Expr INT
```

Here is the resulting program:

```
λΠ> runConvert Source.example
Right ([("a", BOOL), ("x", BOOL)] **
       MkBRes (DeclAdd "a"
                       (And (B False) (Global Here))
                       (DeclAdd "x" (And (B False) (B True)) Empty))
              (Let "y"
                   (Add (I 5) (I 9))
                   (Let "z" (I 6) (Add (Local Here) (Local (There Here)))))) : Either Error
                                                                                      (genv : List (String,
                                                                                                    Ty) **
                                                                                       BuildRes genv
                                                                                                []
                                                                                                INT)
λΠ>
```

## Coda

In this post we have looked at converting a well-typed expression language to a well-typed and well-scoped program.
This was an interesting problem to solved, and aside from incorporating it into my work, I am not sure what other dependent type program enthusiats will make of this.
Not sure if this would make a novel paper or not, but it *is* something work sharing.

### Improvements...

I am hoping that the with-blocks can be turned into do-notation and dependent pairs second argument
accessed using DPair's projection functions...

One interesting improvement here would to not only have `Source` be well-scoped, as well as well-typed, but to use Thinnings to better describe the type of `convert` to ensure that our resulting global and local contexts were originally sourced from the context of source.
I will look at that later.

<!--
-- Local Variables:
-- idris-load-packages: ("containers")
-- End:
-->
