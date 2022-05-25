---
title: Types as Interpreters for HDLs to Graphs.
tags: idris,dependent-types,border-patrol,tdvcs,hdl,systemverilog
...

As part of my PhD I was interested in: _Types as (Abstract) Interpreters_.
This approach embeds an interpretation of your model directly in the type of your terms.
A [previous post](https://jfdm.github.io/post/2015-07-04-nines.html) details it.

As port of my current work I have been investigating the construction of _Hardware Description Languages_ (HDLs) and reasoning about their structure using denotational semantics.
Currently my soundness checks are extrinsic to the intrinsically typed term language I have developed.
It only recently occured to me that we can make these soundness checks intrinsic using the _Types as (Abstract) Interpreters_ approach.

In this post I will describe how we can model a simple core HDL for netlist (derived from Verilog's own syntax and interesting design decisions) and embed a denotation to a multigraph directly in the model's types.
I will also outline more problems that need addressing for this model to be of use.
Of note I have solved these problems but cannot seem to get past the reviewers with the solutions :-(


First we will need some helpers:

```idris
import Decidable.Equality
import Data.Fin
import Data.List.Elem
```

## A Simple Graph

Digital circuits _are_ graphs.
To help with the abstract interpretation we need to have a graph to construct.

The details of how the graph is construct is not required _per se_ to understand the interpretation.
We leave their details for the reader, and note that when adding edges to the graph we ensure that the vertices in the edge are also inserted.
What _is_ important is the kind of graph we require: A Multigraph.
Multigraphs are graphs in which we have a set of vertices, and a list of edges.
We can represent such graphs as:

```idris
record Graph where
  constructor G
  vertices : List Nat
  edges    : List (Pair Nat Nat)
```

**Note** Although we require a _set of vertices_ reasoning about existential quantification (`isElem`) of the `SortedSet` datatype in Idris has not been contributed, and working with Lists is sufficient for our needs.
Provided we ensure the List is a set....

We provide the following API for working with graphs.

```idris
addVertex : Nat -> Graph -> Graph

fromEdges : List (Nat, Nat) -> Graph

addEdge : (Nat, Nat) -> Graph -> Graph

merge : Graph -> Graph -> Graph
```

<!-- idris
addVertex n (G vs es) with (isElem n vs)
  addVertex n (G vs es) | (Yes prf)
    = G vs es
  addVertex n (G vs es) | (No contra)
    = G (n::vs) es


addEdge (a,b) (G vs es) with (isElem (a,b) es)
  addEdge (a,b) (G vs es) | (Yes prf)
    = G vs es
  addEdge (a,b) (G vs es) | (No contra)
    = G vs ((a,b)::es)

fromEdges = foldl addEdge' (G Nil Nil)
  where
    addEdge' : Graph -> (Nat, Nat) -> Graph
    addEdge' g (a,b) = addEdge (a,b) (addVertex b (addVertex a g))


merge a g
  = foldl (flip addEdge) (foldl (flip addVertex) g (vertices a)) (edges a)
-->

## Types

We now provide the types for our little HDL.

First we give the datatypes that determine the shape of channels and ports.
Here the datatypes are _just_ the synthesised subset:

```idris
namespace DataType
  public export
  data DataType = LOGIC | VECT Nat DataType
```

Next we give the types of our terms.

```idris
namespace Ty
```

For ports we also need to denote the expected signal flow which, for simplicity, is uni-directional.

```idris
  namespace Property
    public export
    data Direction = IN | OUT
```

The types for terms capture:

```idris
  public export
  data Ty : Type where
```

Ports in which ports have a shape and a direction.

```idris
    Port : (shape : DataType)
        -> (dir   : Direction)
                 -> Ty
```

Channels are internal wires, and are simply shaped.

```idris
    Chan : (shape : DataType)
                 -> Ty

```

Gates are primitive wiring constructs.

```idris
    Gate : Ty
```

Unit helps us ensure that we know when the end of the specification has been reached.

```idris
    Unit : Ty
```

## Typing Contexts

```idris
namespace Context
```

We will be using an intrinsically typed representation.
As we will be capturing, at the type-level, the denotation of terms we need to construct a typing context that keeps track of the denotations as well as the types.

First we give the denotation of our types to types in our graph construct.

```idris
  public export
  Interp : Ty -> Type
```

Ports map to vertex identifiers.

```idris
  Interp (Port d y)
    = Nat
```

Channels to an edge between two vertices.

```idris
  Interp (Chan s)
    = (Nat, Nat)
```

Gates are a sub-graph.

```idris
  Interp Gate
    = Graph
```

Unit is Unit.

```idris
  Interp Unit
    = Unit
```

With this interpretation we can now specify items in our typing context:

```idris
  public export
  record Item where
    constructor I
```

Items capture the type of a term coupled with the interpretation of the term in terms of a graph.

```idris
    type   : Ty
    denote : Interp type
```

Here we have effectively merged the typing and interpretation environments together!

## Terms

```idris
namespace Term
```

Now with the types and graph constructs define we can now describe how to embed the interpretation of the HDL into its definition.
This is going to be a hairy definition but it is worth it.

First we detail the data structure that represents terms in our HDL.
The type for term takes as 'input', really 'is parameterised by', a counter and a starting graph.
The counter supports unique tagging of vertices, and the starting graph captures the state of the interpretation so far.

```idris
  public export
  data Term : (c_in   : Nat) -> (g_in   : Graph)
```

We then provide the judgement form for terms.
Terms have a typing context and a type.
We also provide the interpretation of the term.

```idris
           -> (ctxt   : List Item)
           -> (type   : Ty)
           -> (denote : Interp type)
```

We then finish the definition with the 'result' of the interpretation.
That is the current state of the accumulator and graph.

```idris
           -> (c_out  : Nat)
           -> (g_out  : Graph)
                     -> Type
    where
```

More formally we might describe this as:

    (c : Nat, g : Graph)[| G |- t : type |] ::= (c' : Nat, g' : Graph, v : [| type |])

Alternatively we might present the interpretation environment explicitly:

    (c : Nat, e : E, g : Graph)[| G |- t : type |] ::= (c' : Nat, g' : Graph, v : [| type |])

With this definition we can now intertwin the definition of our HDLs syntax with its denotation.

### Stop

When we have finished the specification we have also finished the interpretation.
We simply return the current state of the accumulators.


```idris
      Stop : Term c_in g_in ctxt Unit () c_in g_in

```

### Variables

We use De Bruijn indices (proof that an item is in the context) to capture bindings.
Merging the typing context and interpretation environment makes it easier to extra the type and denotation of bound terms.

```idris
      Var : Elem (I ty de) ctxt
         -> Term c_in g_in ctxt ty de c_in g_in

```

### Port introductions

To ensure normal forms we have embedded sequencing of terms within the language's structure, and require that the final expression has type `Unit`.
Only the `Stop` term introduces the `Unit` type.

Thus when introducing ports to the design we model it as a let-binding.
Introducing ports simply extends the typing context with a new bound port.
Ports interpret to _just a vertex_.
Here we must ensure that when diving into the scope (the body of the let-binding) the input accumulator is correctly updated: counter incremented by one; and the vertex embedded in the graph.

```idris
      Port : (dtype  : DataType)
          -> (dir   : Direction)
          -> (scope : Term (S c_in)
                           (addVertex (S c_in) g_in)
                           (I (Port dtype dir) (S c_in) :: ctxt)
                           Unit
                           ()
                           c_out
                           g_out)
                   -> Term c_in  g_in  ctxt Unit ()
                           c_out g_out
```

### Wires

Wires are similarly formed/typed/interpreted as ports.
Instead of ports the wire introduction introduces a channel.
Interpretation of wires maps channels to a subgraph that is a directed edge between two vertices that represent the input and output ports of the channel.

```idris
      Wire : (dtype : DataType)
          -> (scope : Term (S (S c_in))
                           (merge (fromEdges [(S (S c_in), S (S c_in))])
                                  g_in)
                           (I (Chan dtype) (S c_in, S (S c_in)) :: ctxt)
                           Unit
                           ()
                           c_out
                           g_out)
                   -> Term c_in  g_in  ctxt Unit ()
                           c_out g_out
```

### Gates

We now turn our attention to gates.
For simplicity we have considered binary gates only.
The following description naturally extends to n-ary gates, but is somewhat more hairy....

For our HDL binary gates take two inputs and return a single output.
Interpretation of gates are to a sub-graph in which the gate is a single node with two incoming edges and a single outgoing edge...

```idris
      Gate : (outport : Term c_in  g_in ctxt (Port LOGIC OUT) vo
                             c_a   g_a)
          -> (inportA : Term c_a   g_a  ctxt (Port LOGIC IN)  va
                             c_b   g_b)
          -> (inportB : Term c_b   g_b  ctxt (Port LOGIC IN)  vb
                             c_out g_out)
                     -> Term c_in  g_in ctxt Gate (fromEdges [(va, S c_out), (vb,S c_out), (S c_out, vo)])
                             (S c_out) g_out
```

### Gate Instantiation

To include gates into our design (i.e. wire them in) they need to be instantiated.
The `GDecl` term suppots this.
Its design follows that of the introduction of ports and wires.

```idris
      GDecl : (gate : Term c_in  g_in  ctxt Gate g
                           c_mid g_mid)
           -> (scope : Term c_mid (merge g_mid g) (I Gate g :: ctxt) Unit ()
                            c_out g_out)
                   -> Term c_in g_in ctxt Unit ()
                           c_out g_out
```

### Indexing

It is permissible to index vectors on ports.
This will return a single port that is in the same direction.
The interpretation _just_ returns the vertex representing the original port.

```idris
      Index : (port : Term c_in g_in ctxt (Port (VECT size type) dir) v c_out g_out)
           -> (idx  : Fin size)
                   -> Term c_in g_in ctxt (Port            type  dir) v c_out g_out
```

### Projection

We need to be able to access the endpoints of channels.
We do so by projection.
For simplicity we have split the terms in twain, but note they can be merged into a single term.
Project, in both the term language and interpretation, returns the endpoint of the channel.
During interpretation this is the corresponding vertex at the end of the edge.

The direction of projection is counter-intuitive, but is nonetheless intuitive for interpretation.
If we are accessing the 'reading' end of the channel it needs to connect to the inputting port of the primitive term it is being plugged into.
The 'writing' end needs to go to the outputting end.

```idris
      ProjR : (chan : Term c_in g_in ctxt (Chan type)     (s,t) c_out g_out)
                   -> Term c_in g_in ctxt (Port type IN)     t  c_out g_out

      ProjW : (chan : Term c_in g_in ctxt (Chan type)     (s,t) c_out g_out)
                   -> Term c_in g_in ctxt (Port type OUT)  s    c_out g_out
```


With this we have finished the description of the language and its interpretation to a graph.

## Example

We end this tour with simple examples and interactions.

### Example 1

#### Definitions

```idris
example : (c : Nat **
           g : Graph ** Term Z (G Nil Nil) Nil Unit ()
                             c g)
example
  = (_ ** _ **
        Port LOGIC OUT
      $ Port LOGIC IN
      $ Port LOGIC IN
      $ GDecl (Gate (Var (There (There Here)))
                    (Var        (There Here))
                    (Var               Here))
      $ Stop)

```

#### Interactions

```
Main> fst (snd example)
G [1, 3, 4, 2] [(4, 1), (3, 4), (2, 4)]
Main> snd (snd example)
Port LOGIC OUT (Port LOGIC IN (Port LOGIC IN (GDecl (Gate (Var (There (There Here))) (Var (There Here)) (Var Here)) Stop)))
Main> :t snd (snd example)
snd (snd example) : Term 0 (G [] []) [] Unit () 4 (G [1, 3, 4, 2] [(4, 1), (3, 4), (2, 4)])
Main>
```

### Example 2

#### Definitions

```idris
example2 : (c : Nat ** g : Graph ** Term Z (G Nil Nil) Nil Unit ()
                                         c g)
example2
  = (_ ** _ **
       Port LOGIC OUT
     $ Port LOGIC IN
     $ Wire LOGIC
     $ GDecl (Gate (ProjW (Var        Here))
                   (Var        (There Here))
                   (Var        (There Here)))

     $ GDecl (Gate (Var        (There (There (There Here))))
                   (ProjR (Var               (There Here)))
                   (ProjR (Var               (There Here))))
     $ Stop)
```

#### Interactions

```
Main> fst (snd example2)
G [2, 5, 3, 1, 6, 4] [(2, 5), (5, 3), (4, 4), (6, 1), (4, 6)]
Main> snd (snd example2)
Port LOGIC OUT (Port LOGIC IN (Wire LOGIC (GDecl (Gate (ProjW (Var Here)) (Var (There Here)) (Var (There Here))) (GDecl (Gate (Var (There (There (There Here)))) (ProjR (Var (There Here))) (ProjR (Var (There Here)))) Stop))))
Main> :t snd (snd example2)
snd (snd example2) : Term 0 (G [] []) [] Unit () 6 (G [2, 5, 3, 1, 6, 4] [(2, 5), (5, 3), (4, 4), (6, 1), (4, 6)])
```

## Problems

This is a *very* simple illustrative example, that does not do everything we need it to do.

1. We have not taken into account bi-directional ports.
   There are tricks we need to do to ensure that we can _plug-in_ bi-directional ports into gates.

   I will explain these tricks in another post.

2. We have not taken into account the correctness of the resulting graph.
   This will require extending the definition of `Stop` with a correctness predicate over the graph.

   I will explain the approach I take in another post.

3. Going from raw SystemVerilog terms to this core representation.
   If not dealing with bi-directional ports, this elaboration is not complicated.
   For bi-directional ports we are going to need some clever elaboration to ensure the correct plugging of wires.

   I will explain the approach I take in another post.

4. We have not reasoned about the usage of ports in this setting.
   Our language provides unrestriced wiring which can lead to accidental fan-outs, or even worse accidental fan-ins.

   Even if we provide a multiplexer primitive, we need something special in the type-system to ensure wire usage is _linear_.

   I will explain the approach I take in another post/paper.

## Coda

This post should have demonstrated how dependent types helps us to write more precise software where extrinsic checks (in this case abstract interpretation) can be embedded directly into the 'types' of our terms.
With this approach we can design new HDLs in which the wiring structure is not only correct at compile time but that our approach is provable sound.
Before my soundness checks were extrinsic, here they are intrinsic.

What will be interesting will be to write the elaborator/type-checker and see if we can erase the checks for runtime...
