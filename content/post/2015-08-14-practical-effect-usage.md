---
title: "Tips for using Effects in Idris"
tags: ["idris","effects","tips"]
date: 2015-07-28
---

`Effects` is an Idris package that implements resource-dependent algebraic effects.
This allows a developer to control at a fine-a-grained level the side affects (state, logging, IO) for effectful programs.
A tutorial and more background on their use is [available on line](https://idris.readthedocs.org/en/latest/effects/index.html#eff-tutorial-index).

When writting my Idris libraries I have used Effects to manage exceptions, state, logging, and IO.
Here are some tips in my experiences in using Effects.


## Global Effects List

In an effectful function the effects used are declared in a `List` data structure of type `List EFFECT`.
An effectful main function will look like:

```idris
fooMain : Eff () [FILE_IO, STDIO, SYSTEM]
fooMain = do
   ...
```

The top most list of effects will determine the complete set of effects allowed in sub-effectful programs.
Good practice will be

In this list the order in which effects appear will have an effect on the order in which sub lists can be created for effectful programs called.
An engineering tip will be to create a global list of effects that allows for the list of effects to be passed around to all effectful programs.
It also saves on typing.

## `Effs.idr`

Most, if not all, of my projects have a file called `Effs.idr`.
This file is used to control the imports of effects, and creation of effectful utility functions for working with state, logging, and IO.
This allows me to keep track of the effects I use and isolate the majority of utility functions to a single file.

## Labelling Effects.

If you are creating a library to be used by others that contains effectful functions, be proactive and label the effects that are native to your library.
For example, the file, stdio, log, and system effects are shared by all effectful programs and need not be labelled.
The use of effects such as exception and state will be custom to your library.
This advice holds if you are using only a single instance of the State effect, as it will be guaranteed that a user might use a library that has their own effect.
Label it.

These labels should be unique and a simple naming scheme can be =<name of package><descriptive term>=.
For example:

+ Exceptions in Foo would be labelled =fooerr=
+ State in Foo would be labelled =foostate=

The only place in which you would not want to label your state effect if you know that the effect will be run in isolation from the main effectful program.

## Hiding Labels

With the use of labels can come messy looking code and forgetfulness of label names.
The latter especially if you hide the list of effects.

Take for example:

```idris
FooEffs : List EFFECT
FooEffs = [ FILE_IO (), SYSTEM, STDIO
          , 'foost ::: STATE FState
          , 'fopts ::: STATE FOpts
          , 'foosymtbl ::: STATE SymTbl
          , 'fooerr ::: Exception FooError]

fooMain : Eff () FooEffs
fooMain = do
  as <- getArgs
  opts <- processArgs as
  case opts of
    Nothing => 'fooerr :- raise InvalidOpts
    Just os => do
      'fopts :- put os
      st <- doInit
      case st of
        Nothing => 'fooerr :- raise InvalidState
        Just s => do
          'foost :- put st
          doStuff ...
```

A good trick is to re-domain the effects such that the effectful functions are accessed using the form =<package name>.<function name>=, or are placed in a wrapper functions.
For example, take the Exception effect:

```idris
namespace Foo
  raise : FooError -> Eff b ['fooerr ::: Exception FooError]
  raise err = 'fooerr :- Exception.raise err
```


Accessing state becomes:

```idris
getFState : Eff FState ['foost ::: STATE FState]
getFState = 'foost :- get

updateFState : (FState -> FState) -> Eff () ['foost ::: STATE FState]
updateFState u = 'foost :- update (\st => u st)

setFState : FState -> Eff () ['foost ::: STATE FState]
setFState newST = 'foost :- put newST
```

And option accessors will have type:

```idris
getFOptions : Eff FOpts ['fopts ::: STATE FOpts]
putFOptions : FOpts -> Eff () ['fopts ::: STATE FOpts]
```

The program from above now becomes:

```idris
fooMain : Eff () FooEffs
fooMain = do
  as <- getArgs
  opts <- processArgs as
  case opts of
    Nothing => Foo.raise InvalidOpts
    Just os => do
      setFOptions os
      st <- doInit
      case st of
        Nothing => Foo.raise InvalidState
        Just s => do
          setFState s
          doStuff ...
```

An added benefit of this approach is that it adds a level of indirection in case you wish to update how you deal with your  state affects...
Which leads on to the final hint for using effects.

## Collapse State Effects

If you find that you are using multiple state effects in your program that you define yourself, consider collapsing them into a single record and write some wrapper effectful functions to obtain the requisite state from the global state.
