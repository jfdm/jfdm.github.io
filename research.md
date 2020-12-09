---
title: Engineering should be TyDe
...

## Interests

Generally speaking, I am interested in how we can take state-of-the-art advances in programming language theory, namely type-systems \& functional programming, and use these advances to fundamentally change how we design systems to make them more trustworthy: Secure and Safe.

Specifically, I am interested in bettering system design and construction through applications of:

+ functional programming;
+ formal verification;
+ mathematically informed programming;
+ dependent types;
+ sub-structural typing (quantitative, resource-dependent, session); and
+ algebraic effect handlers.

There are more topics that I am interested in, but the above keeps me busy for now!

## Vision

In Welsh English, the word 'tidy' describes anything positive, pleasurable, good, neat *et cetera*.
How we engineering our Computer Systems is not tidy nor trustworthy.
Today's systems use a specification that is separate from the implementation, and their deployment requires that we verify that implementations adhere to specifications through external processes.
There is a fundamental separation-of-concerns between system: *specification*---by domain experts; *verification*---by verification experts; *creation*---by software engineers; *use*---by end users; and *certification*---by auditors.
Such a disconnect leads to issues over system security and safety by allowing errors to be present throughout a system's lifecycle.
Allowing our computer systems to be a clear and present risk to national, and personal safety and security by possessing potentially exploitable vulnerabilities.
I want to fundamentally change the way we engineer systems.
I believe that if we are to ever build trustworthy (tidy) systems, we must make machine checkable specifications an intrinsic aspect of the system through adoption of type-driven approaches.
By doing so we can:
reduce mismatches between a system's specification and implementation;
increase productivity of system creation and verification; and
fundamentally enhance system trustworthiness.
This will impact both Society and The Economy by guaranteeing that our systems are trustworthy because our engineering practises are themselves: **Ty**pe **D**riv**e**n!

## Projects

+ [**AppControl**](https://dsbd-appcontrol.github.io) is an [EPSRC funded research project](https://gow.epsrc.ukri.org/NGBOViewGrant.aspx?GrantRef=EP/V000462/1) that is part of the Industrial Strategy Challenge Fund: [Digital Security by Design](https://epsrc.ukri.org/funding/calls/iscf-digital-security-by-design-research-projects/).
The project is a collaboration between the Universities of Glasgow, Imperial College London, and Essex.
This project's goal is to improve upon the trustworthiness of Hardware/Software Co-Design by combining the results of **Border Patrol** with that of Capability Hardware as developed by the [CHERI Program](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/dsbd.html).


+ [**Border Patrol**](https://border-patrol.github.io) is an [EPSRC funded research project](http://gow.epsrc.ac.uk/NGBOViewGrant.aspx?GrantRef=EP/N028201/1) that is part of the [Trust, Identity, Privacy and Security in the Digital Economy](https://www.epsrc.ac.uk/funding/calls/trustidentityprivacysecurity/) call.
The project is a collaboration project between the Universities of Glasgow, Heriot-Watt, and Imperial College London.
The project's goal is to make the design of hardware systems, and in particular smart devices, resiliant against hidden malicious functionality by ensuring that devices only do what is expected of them. It is an ambitious project that combines state-of-the-art advances in type theory and compiler technology, and applies them to hardware design.

+ **Idris** is a general purpose dependently typed language.
I have been involved with the project for many years as developer and community participant.
I help administer the Github project pages for the compiler and community.

<!--
+ **BiGraphER** I am currently getting involved with the [BigraphER project](http://www.dcs.gla.ac.uk/~michele/bigrapher.html).
Bigraphs are an interesting formalism for modelling communicating systems.
I am applying my expertise in dependent types to help further reason about domain specific bigraphical models.
-->

### Previous Projects

+ **Security by Design and Construction** was a six-month project looking at type-driven verification of communicating systems. I was employed as an RA to investigate how to use dependent types and algebraic effect handlers to reason about communicating systems.

+ **Type-Driven Verification of Communicating Systems** was a one year EPSRC first grant to investigate the use of dependent types to reason about communicating systems. I was responsible for development of a *Multiparty Session Type* inspired EDSL and corresponding runtime.


## Software

Software that I develop for both work and other reasons.
There are more repo's on GitHub but I will list important ones here.

### Research

+ @sif-lang
+ @idris-xml
+ @idris-grl
+ @idris-containers
+ @idris-config
+ @idris-argparse
+ @edda


### Other

+ @sta-latex
