---
title: "ICFP Rejection"
tags: ["idris","tdvcs","paper","icfp","rejection"]
date: 2017-03-28
---


I submitted a paper entitled *Type-Driven Development of Communicating Systems* to [ICFP '17](https://icfp17.sigplan.org/).

I have decided to uploaded the abstract here so that my attempt is a least indexable by the great machine spirit in the web---Hallowed be thy API.
Given time I will also upload a copy of the paper to ArXiV.

The paper's abstract was:

> Communication protocols are a cornerstone of modern system design.
> However, there is a disconnect between the tooling used to design,
> implement and reason about these protocols and their
> implementations.  Session Types offer a typing discipline that helps
> resolve this difference by allowing protocol specifications to be
> used during type-checking, ensuring that implementations adhere to a
> given specification.  Session Type implementations are limited in
> their expressiveness in protocol design and implementation.
>
> In this paper we describe `Sessions`, an adaptation of Session Types
> in the dependently typed language Idris, and demonstrate the ability
> of `Sessions` to describe several common protocols.  We also present
> `NetworkDSL` a separate EDSL that realises two-party sessions for
> network communication.
>
> Our work improves upon existing Session Type implementations by
> introducing value dependencies between messages and fine-grained
> channel management during protocol design and implementation.  We
> also use Idris' support for EDSL construction to allow protocols to
> be designed and reasoned about in the same language as their
> implementation.  Thereby allowing for an intrinsic bond to be
> introduced between a protocol's specification and its
> implementation, and also with their verification.
>
> By using dependent types we can reduce further the existing
> disconnect between the tooling used for protocol design,
> implementation, and verification.
