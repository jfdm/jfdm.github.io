---
title: "An Effectful Logger: Part One"
tags: ["idris","effects","tips"]
---

`Effects` is an Idris package that implements resource-dependent algebraic effects.
This allows a developer to control at a fine-a-grained level the side affects (state, logging, IO) for effectful programs.
A tutorial and more background on their use is [available on line](https://idris.readthedocs.org/en/latest/effects/index.html#eff-tutorial-index).

In the past I wrote some Logging effects as a means to understand how resource-dependent algebraic effects work.
Recently, I had need to use it in anger in my application.
As a result I rewrote the damm thing, and decided to describe the output in a blog post.
This post will describe the simple logging model, with a future post describing the category based model.

## Logging

Put simply logging is a tool used to control the export of information about a programs execution, typically informing the system (and user) about what the program is up to.
To control the verbosity of information being displayed most logging infrastructure's support logging levels.
For example, Idris has a simple numerical level on a range on 0--9, however, this approach does offer a few limitations.

First, what is going to be shown at each level is not necessarily clear.
This can be [abated through documentation](https://idris.readthedocs.org/en/latest/reference/compilation.html), and well-named functions, the different levels are not ingrained within the logging infrastructure.
This could be construed as a developer-oriented usability problem; trying to remember what each level is used for.

Secondly, one can only control the level of debugging and not categories of information.
Within the Idris compiler there are various stages of compilation that will interest developers at different times.
For example, those working on code generation will want to **only** view the logging for the code generator; and those interested on parsing the parsing infrastructure.

## Logging Model

The logging modelled in the Logging effects is based upon the Log4j/Python logging families.
Logging levels are within a numerical range with zero indicating no logging and the upper bound indicating that we log all the things.
Within this range there are a series of maximal points that indicate different semantic logging levels.
Typically these levels are in order:

OFF
: No logging.

TRACE
: A fine-grained debug message, typically capturing the flow through the application.

DEBUG
: A general debugging event.

INFO
: An event for informational purposes.

WARN
: An event that might possible lead to an error.

ERROR
: An error in the application, possibly recoverable.

FATAL
: A severe error that will prevent the application from continuing.

ALL
: All events should be logged.

Naturally, one would wish to model logging as a `Nat`, with predefined variables to store and remember the different logging levels.
However, pattern matching and working with natural numbers in Idris w.r.t. to logging would be slightly painful, especially if you wish to process logging events based upon their levels.
Also this is dependent types and we can do better.

```idris
data LogLevel : Nat -> Type where
  OFF    : LogLevel 0
  TRACE  : LogLevel 10
  DEBUG  : LogLevel 20
  INFO   : LogLevel 30
  WARN   : LogLevel 40
  ERROR  : LogLevel 50
  FATAL  : LogLevel 60
  ALL    : LogLevel 70
  CUSTOM : (n : Nat) -> {auto prf : LTE n 70} -> LogLevel n
```

In our model, we have embedded within the type the natural number representation for each logging levels.
With dependent types we have combined the power of algebraic data types with abstract interpretations.
When defining custom logging levels an auto implicit argument is used to constraint the level to with the range.

**Note** it becomes clear in this logging model that for each semantic level there are sub-levels either side that can be (ab)used.
For example, verbosity levels of tracing output can be modelled as follows:

```idris
traceSalient : LogLevel 7
traceSalient = CUSTOM 7

traceMinimal : LogLevel 8
traceMinimal = CUSTOM 8

traceLight : LogLevel 9
traceLight = CUSTOM 9

traceMore : LogLevel 11
traceMore = CUSTOM 11

traceMuch : LogLevel 12
traceMuch = CUSTOM 12

traceAlot : LogLevel 13
traceAlot = CUSTOM 13
```

Further, an improvement will be to allow developers to provide an optional string description for the custom logging levels.

How log levels are compared and printed are left as a exercise to the reader. As a hint, *it is in the type*.

## The Resource

With the logging level model defined, a simple logging effect can be considered.
Within resource-dependent effects the effect operates over a resource.
For logging this will be the logging level of execution.

Although this level can be used directly, the dependent nature of `LogLevel` construction can make things harder and we would have to use a dependent effect.
The latter I am not to sure about.
So to ease use, the logging level can be wrapped in a simple record which is given a default value of `OFF`.

```idris
record LogRes where
  constructor MkLogRes
  getLevel : LogLevel n

instance Default LogRes where
  default = MkLogRes OFF
```

We are now free to construct the logging effect.

## The Effect

The logging effect is a rather simple effect, that allows for the level of logging to be set (`SetLvl`) and for a logging message to be logged at a certain level---`Log`.
The type signatures for these two effectful function definitions show how for `SetLvl` the resource changes, and for `Log` it does not.

```idris
data Logging : Effect where
  SetLvl : (lvl : LogLevel n) -> sig Logging () (LogRes) (LogRes)

  Log : (lvl : LogLevel n)
     -> (msg : String)
     -> sig Logging () (LogRes)
```

**Remark** Although the effect is not a dependent effect, it would be nice to capture the change in logging level w.r.t to the resource.
However, I do not know how to do this.


## The Effect Handler

The next stage is to construct a handler to instruct Idris how to deal with Logging in the IO context.

```idris
instance Handler Logging IO where
  handle res (SetLvl newLvl) k = k () (MkLogRes newLvl)

  handle res (Log lvl msg) k = do
    case cmpLevel lvl (getLevel res)  of
      GT        => k () res
      otherwise =>  do
        putStrLn $ unwords [show lvl, ":", msg]
        k () res
```

For changing the logging level, this requires the resource to be updated with the new level.

For logging information, we first have to determine if we should display the information or not.
A custom compare function `cmpLevel : LogLevel a -> LogLevel b -> Ordering` has been defined as part of the log level model is used to determine if the level of the message is within the allowed range.
One way to think about this action is that by default the logging level is a closed range.
By increasing the logging level more levels of access are made available.
If the logging level of the message falls within this range then it can be used, otherwise, move on.

Within the handler:
`res` is the resource we are operating over;
`k` is a continuation that requires the return type (Unit for these functions), and the value of the resource.


## The Effect Descriptor

```idris
LOG : EFFECT
LOG = MkEff (LogRes) Logging
```

With the handler and effect defined, the effect descriptor is given as being an descriptor with the resource `LogRes` for `Logging` effect.
This descriptor is what the developer is presented with in their list of effects.

## The Effectful API

The final act is constructing the simple logging effect is to provide the API.

### Set logging Level

Changing the logging level is implemented as follows:

```idris
setLogLvl : (l : LogLevel n) -> Eff () [LOG]
setLogLvl l = call $ SetLvl l
```

### Log to a Known Level

For each of the known levels a effectful function can be created that logs the given message at the appropriate level.

```idris
trace :  String -> Eff () [LOG]
trace msg = call $ Log TRACE msg

debug :  String -> Eff () [LOG]
debug msg = call $ Log DEBUG msg

info :  String -> Eff () [LOG]
info msg = call $ Log INFO msg

warn :  String -> Eff () [LOG]
warn msg = call $ Log WARN msg

fatal :  String -> Eff () [LOG]
fatal msg = call $ Log FATAL msg

error :  String -> Eff () [LOG]
error msg = call $ Log ERROR msg
```

Logging functions for `OFF` and `ALL` have not be provided as they are purely there to indicate bounds.
Although, for completeness one could provide functions.

### Custom Level.

To log to a custom level (for example light tracing), one can specify the level directly as a natural number.

```idris
log : (l : Nat) -> {auto prf : LTE l 70} -> (m : String) -> Eff () [LOG]
log l msg = call $ Log (getProof lvl) msg
  where
    lvl : (n ** LogLevel n)
    lvl = case cast {to=String} (cast {to=Int} l) of
            "0"  => (_ ** OFF)
            "10" => (_ ** TRACE)
            "20" => (_ ** DEBUG)
            "30" => (_ ** INFO)
            "40" => (_ ** WARN)
            "50" => (_ ** FATAL)
            "60" => (_ ** ERROR)
            _    => (_ ** CUSTOM l)
```

Unfortunately some helper code is required to ensure that the predefined levels are used.

**Remark**
Having wrote this blog post, maybe one should rename this `logN` for logging with the natural number representation, and allow developers to specify directly the logging level using the `LogLevel` type...............

## Minimal Logging Example

To show the Effect in action a minimal logging program is (which is a derivation of the test):

```idris
import Effects
import Effect.StdIO
import Effect.Logging.Default

doubleFunc : Nat -> Eff Nat [LOG]
doubleFunc x = do
  warn $ unwords ["Doing the double with", show x ]
  pure (x+x)

eMain : Maybe (LogLevel n) -> Nat -> Eff () [STDIO, LOG]
eMain Nothing    x = printLn !(doubleFunc x)
eMain (Just lvl) x = do
  setLogLvl lvl
  printLn !(doubleFunc x)

main : IO ()
main = do
   run (eMain Nothing    3) -- No logging
   run (eMain (Just ALL) 4) -- Log everything
```

## The End

And that is it... The hardest part about creating the effect was understanding how to use the `Effects API`.
In the future I shall describe how to construct a logging effect based on categories and numerical levels.

## Next Steps

+ How to improve the logger so that logging information can be sent to:
  + Files
  + Logging Server
+ How to provide logging formatters to make the logging output user defined.
