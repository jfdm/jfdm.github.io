---
title:  "A Short Note on Collecting Dependently Typed Values"
tags: ["idris","dependent-types","paper"]
date: 2018-08-07
---

I've finally found a _round tuit_ down the back of the sofa and worked out how to a) use arXiv for publishing preprint eprints, and b) publishing a short note on collecting dependently typed values.

The URL is: https://arxiv.org/abs/1808.09234


The work stems from a short note I wrote in the appendix of my PhD thesis, which in turn [originated as a blog post](2015-07-05-dependent-lists.html).
It is not necessarily novel work, or worthy of publication at a workshop, but thought I would share nonetheless.

>   Within dependently typed languages, such as Idris, types can depend on values.
>  This dependency, however, can limit the collection of items in standard containers: all elements must have the same type, and as such their types must contain the same values.
>  We present two dependently typed data structures for collecting dependent types: \IdrisType{DList} and \IdrisType{PList}.
>  Use of these new data structures allow for the creation of single succinct inductive \acsp{adt} whose constructions were previously verbose and split across many data structures.

Enjoy.
