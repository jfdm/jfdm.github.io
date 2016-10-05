---
title: Effectful Channel Management
tags: idris,effects,sessions,tdvcs
...

Communicating systems require channels to communicate, in many of the
programming languages that provide communication channels the management
of these channels at the application layer is left to the programmer to
get right. That is, the programmer is responsible for ensuring that the
channel is established, connected to, and then destroyed.

In languages that support dependent types we can encoded, at the type
level, extra properties about our software program. Further, the idea
of algebraic effects supports the separation of a program's
description from its realisation in different contexts. Edwin Brady's
`EFFECTS` library has shown how this is possible using dependent types
[@Brady2015rda]. The implementation of `EFFECTS` allows for efficient
management of a program's side-effects and dealings with the outside
world. See the *Effects Tutorial* [for more information](http://idris.readthedocs.io/en/latest/effects/index.html).

The `FILE` Effect
=================

An interesting aspect of `EFFECTS` is that each effect is associated
with a resource. For the `FILE` effect it is a file handler, for the
`LOG` and `PERF` effects that I contributed to `EFFECTS` it is logging
levels and captured metrics. With resource based algebraic effects we
can capture (at the type level) the allowed (state) changes to this
resource. If we [examine the current `FILE` effect from Idris' effects
library](https://raw.githubusercontent.com/idris-lang/Idris-dev/master/libs/effects/Effect/File.idr)
you can see this for file access. The resource for the `FILE` effect is
the file descriptor and its relation to the mode of operation.

``` {.idris}
||| The file handle associated with the effect.
|||
||| @m The `Mode` that the handle was generated under.
data FileHandle : (m : Mode) -> Type where
    FH : File -> FileHandle m
```

The `FILE` effect is a dependent effect in that the result of the
effectful operation is used to calculate the value of the resource being
computed over. Given the function `calcResourceTy`:

``` {.idris}
calcResourceTy : (m  : Mode)
              -> (ty : FileOpReturnTy fOpTy retTy)
              -> Type
calcResourceTy _ (FError e) = ()
calcResourceTy m _          = FileHandle m
```

`calcResourceTy` computes the type of the resource as being unit if
there is a failure, and if not the resource is the `FileHandle`
parameterised by the mode of operation. When combined with the mode of
operation we can have a more informed means to calculate the next value
of the resource.

``` {.idris}
  ||| An effect to describe operations on a file.
  data FileE : Effect where

    -- Open/Close

    Open : (fname : String)
        -> (m : Mode)
        -> sig FileE
               (FileOpReturnTy SUCCESS ())
               ()
               (\res => calcResourceTy m res)
....
```

Communication is Communication
==============================

But why talk about the `FILE` effect? Well if we think about it, reading
and writing with a file is analogous to communicating over a channel. We
have to:

1.  establish access to the file (set up a means to communication);
2.  read or write to the file (receive or send messages); and
3.  shutdown access to the file (shut down the means of communication).

So why not apply creation of a file effect to management of a
communication channel?

Fortunatly, Idris comes with an [unsafe means to perform concurrent
communication between different Idris
processes](https://github.com/idris-lang/Idris-dev/blob/master/libs/base/System/Concurrency/Channels.idr)
(and IPC too). Edwin has shown how we can reason about communication in
Idris at [Lambda
World](https://twitter.com/edwinbrady/status/782165539514875904), and
**spoiler alert** in the TDD book too.

However, over the summer I took a stab at using effects to manage
channels. This [was inspired by earlier work by Simon
Fowler](https://github.com/SimonJF/IdrisNet2).

For the remainder of this post, I shall describe my implementation of a
resource based algebraic effect for channels.

The Resource
============

Like the `FILE` effect we are going to model an active session using a
simple resource `OpenSesh`, and parameterise it by the state of the
channel represented by the enumerated type `SSTATE`.

``` {.idris}
data SSTATE =  Unconnected | Spawned | Active
```

Channels are either: *Unconnected*---literally unconnected;
*Spawned*---alive but not communicating; or *Active*---are communicating
with another entity. `OpenSesh` is defined as follows:

``` {.idris}
data OpenSesh  : (st : SSTATE) -> Type where
   NoSesh      : OpenSesh Unconnected
   SpawnedSesh : (pid : PID) -> OpenSesh Spawned
   ActiveSesh  : (pid : Maybe PID) -> (sesh : Channel) -> OpenSesh Active
```

Here an unconnected channel is specified using `NoSesh` and contains no
information. `SpawnedSesh` represents a spawned process, so we must
capture the processes `PID`. `ActiveSesh` represents either a client
channel or server channel. If the channel is connecting to another
process, not only do we need the channel to communication on, but also
the `PID` of the process. If we are the server process, we need to keep
track of the communication channel only.

Helpers
=======

Before we define the effect we first define some helper code.

Type Synonyms
-------------

First, type synonyms.

``` {.idris}
INIT : Type
INIT = OpenSesh Unconnected

WAIT : Type
WAIT = OpenSesh Spawned

ACTIVE : Type
ACTIVE = OpenSesh Active
```

State
-----

The allowed state transitions between resource types. We have decided
that we shall use a `Bool` to describe success or not.

### Connecting to a Process

1.  As a Client

    If connection was successful then move to active, otherwise go back
    to wait.

    ``` {.idris}
    connectedOK : Bool -> Type
    connectedOK False = OpenSesh Spawned
    connectedOK True  = OpenSesh Active
    ```

2.  As a Server

    If attempt to listen was successful then move to active, otherwise
    go back to unconnected.

    ``` {.idris}
    listenedOK : Bool -> Type
    listenedOK False = OpenSesh Unconnected
    listenedOK True  = OpenSesh Active
    ```

### Sending Messages

If message was sent then stay active, otherwise there was a failure and
move to unconnected.

``` {.idris}
sentOK : Bool -> Type
sentOK True  = OpenSesh Active
sentOK False = OpenSesh Unconnected
```

### Receiving Messages

If message was received then stay active, otherwise there was a failure
and move to unconnected.

``` {.idris}
receivedOK : Maybe a -> Type
receivedOK (Just v) = OpenSesh Active
receivedOK Nothing  = OpenSesh Unconnected
```

The `CHANNEL` Effect
====================

With the helper code defined, we can now describe an effectful means to
manage processes. To do so we have to use a mutual block to allow an
effectful process to spawn a second effectful process.

``` {.idris}
mutual
  ProcessE : (st      : Type)
          -> (rTy     : Type)
          -> (inEffs  : List EFFECT)
          -> (outEffs : List EFFECT)
          -> Type
  ProcessE st ty inEffs outEffs = Eff ty
                                      (CHANNEL st :: inEffs)
                                      (\_ => (CHANNEL st :: outEffs))

  ||| The effectful description for `Session`.
  data ChannelE : Effect where

    ||| Spawn an effectful process to communicate with, transitioning
    ||| from `INIT` to `WAIT`.
    Spawn : Env IO esi
         -> ProcessE INIT () esi eso
         -> sig ChannelE (PID) (INIT) (WAIT)

    ||| Connect to a spawned process, transitioning from `INIT` to
    ||| result of `connectedOK`.
    Connect : sig ChannelE (Bool) (WAIT) (\res => connectedOK res)

    ||| Listen for a connection, traisitioning from `INIT` to result
    ||| of `listenedOK`.
    Listen : (tout : Int)
          -> sig ChannelE (Bool) (INIT) (\res => listenedOK  res)

    ||| Send a message of type `a`, transitioning from `ACTIVE` to
    ||| result of `sentOK`.
    Send : a -> sig ChannelE (Bool) (ACTIVE) (\res => sentOK res)

    ||| Receive a message of type `a`, trasitioning from `ACTIVE` to
    ||| result of `receivedOK`.
    Recv : (a : Type)
        -> sig ChannelE (Maybe a) (ACTIVE) (\res => receivedOK res)

    ||| End a session, trasitioning back to `INIT`.
    End : sig ChannelE () (ty) (INIT)


  ||| An effectful API for `System.Concurrency.Sessions`.
  |||
  ||| @st The state the session is in.
  CHANNEL : (st : Type) -> EFFECT
  CHANNEL st = MkEff st ChannelE
```

If we examine the description of the effectful functions, we can see the
allowed state transitions between different API calls. For example,
spawning a process will transition the effect from being unconnected to
waiting. Then we can only progress to an active session if connecting to
the spawned resource was successful. Similar transitions are encoded in
the effect between the different operations.

Implementation for IO.
======================

With the effect specified, we can now define an implementation for this
effect for the `IO` context. This handler will describe how to realise
the management tasks described in the effect. For concurrent processes
this will require spawning processes, connecting to processes, listening
for processes, sending and receding messages, and closing sessions down.

``` {.idris}
Handler ChannelE IO where

  handle NoSesh (Spawn env proc) k = do
      pid <- spawn $ runInit (NoSesh::env) (proc)
      k (pid) (SpawnedSesh pid)

  handle (SpawnedSesh pid) Connect k = do
      msesh <- connect pid

      case msesh of
          Nothing      => k False (SpawnedSesh pid)
          r@(Just res) => k True  (ActiveSesh (Just pid) res)

  handle (NoSesh) (Listen tout) k = do
      msesh <- listen tout

      case msesh of
          Nothing      => k False NoSesh
          r@(Just res) => k True  (ActiveSesh Nothing res)

  handle st@(ActiveSesh pid sesh) (Send m) k = do
      sent <- unsafeSend sesh m
      if sent
        then k True st
        else k False NoSesh

  handle st@(ActiveSesh pid sesh) (Recv ty) k = do
      res <- unsafeRecv ty sesh
      case res of
        Nothing    => k Nothing    NoSesh
        (Just val) => k (Just val) st

  handle st End k = k () NoSesh
```

Effectful API
=============

With the effect and handler defined, we can now present the API that the
developer can use to program with.

Describing a process.
---------------------

A `Process` is a function that can communicate using the session effect.
We use this alias to make describing communicating processes that little
bit easier.

Note that the definition of `Process` already specifies the session
required for communicating.

``` {.idris}
Process : (st  : Type)
       -> (rTy : Type)
       -> (es  : List EFFECT)
       -> Type
Process st ty inEffs = ProcessE st ty inEffs inEffs
```

Spawning, Connecting, and Listening
-----------------------------------

Attempt to spawn an effectful process that communicates using a
`Sessions`. Returning the `PID` of the spawned process.

``` {.idris}
spawn : (env  : Env IO es)
     -> (proc : Process INIT () es)
     -> Eff (PID)
            [CHANNEL INIT]
            [CHANNEL WAIT]
spawn env proc = call $ Spawn env proc
```

Attempt to establish a connection to the spawned process. The function
can only be used once a session has been spawned.

``` {.idris}
connect : Eff (Bool)
              [CHANNEL WAIT]
              (\res => [CHANNEL (connectedOK res)])
connect = call $ Connect
```

Listen for a fixed amount of time for a connection from an external
process. The function is used by the spawned process to accept incomming
requests.

``` {.idris}
listen : (timeout : Int)
      -> Eff (Bool)
             [CHANNEL INIT]
             (\res => [CHANNEL (listenedOK res)])
listen t = call $ Listen t
```

Message Passing
---------------

Send a message of type `ty`. Returning a `Bool` describing success.

``` {.idris}
send : (msg : ty)
    -> Eff Bool
           [CHANNEL ACTIVE]
           (\res => [CHANNEL (sentOK res)])
send msg = call $ Send msg
```

Expect to receive a message of the specifyed type. This is unsafe as
receive **expects** the incomming message to be of the specified type.

``` {.idris}
recv : (ty : Type)
    -> Eff (Maybe ty)
           [CHANNEL ACTIVE]
           (\res => [CHANNEL (receivedOK res)])
recv ty = call $ Recv ty
```

Stopping the Session
--------------------

``` {.idris}
stop : Eff () [CHANNEL ty] [CHANNEL INIT]
stop = call End
```

Example
=======

We finish of this post by showing the code for a game of ping pong.

First we describe the called process `ping`.

``` {.idris}
ping : Process INIT () [STDIO]
ping = do
  True <- listen 10
          | False => stop
  True <- send "ping"
          | False => stop

  msg <- recv String
  case msg of
    Nothing => pure ()
    (Just v) => do
        putStrLn "Ping received"
        printLn v
        stop
```

Notice, that in the code we have to explicitly stop and terminate the
process upon failure. If we remove these statements, the program will
not compile as we have violated the transitions described in the effect.
Further, if we try to send a message before we have connected, Idris
will complain further.

Below `pong` is the client process that initiates the game of ping pong.

``` {.idris}
pong : Process INIT () [STDIO]
pong = do
  pid <- spawn [()] ping
  True <- connect | False => stop
  msg <- recv String
  case msg of
    Nothing => stop
    (Just v) => do
        putStrLn "pong received"
        printLn v
        True <- send "pong" | False => pure ()
        stop
```

Again we must call `spawn` before we call `connect` and both before we
can send or receive messages.

We can play the game of ping pong by running the effectful program
specifying that we expect two sessions to be used.

``` {.idris}
play : IO ()
play = runInit [NoSesh,NoSesh] pong
```

The End.
========

This post describes how effects can be used to manage our communication
channels. [A full code listing is available online](https://gist.github.com/jfdm/52904b466298f1e53da5f43c723f01ac).

However, the communication over these channels is not type
safe. [Edwin demonstrated one means of ensuring such type safe communication at Lambda World 2016](https://twitter.com/edwinbrady/status/782165539514875904). However, there are some other things we can do that are more advantageous and cooler. /Yes, there is more cooler stuff that what Edwin demonstrated at Lambda World./
My research is currently focused on not only how to manage channels using dependent types but how to type check the communication itself.

Hopefully I will blog more about what I am up to, I do have some things in the pipeline that I won't share just yet as they are not complete.

References
==========
