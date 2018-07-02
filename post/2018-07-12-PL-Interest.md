---
title:  Type-Systems for Describing System-on-a-Chip Architectures.
tags: idris,soc,hardware,linear-types,dependent-types,border-patrol,tdd,pl-interest
...

I am giving a talk about my work on the [Border
Patrol Project](https://border-patrol.github.io) at the University of
Edinburgh, [School of Informatics(https://www.ed.ac.uk/informatics), [PL-Interest](http://wcms.inf.ed.ac.uk/lfcs/research/groups-and-projects/pl/programming-languages-interest-group) Group.

This extends upon my talk from March to the FP-Group at
St Andrews with a more complete picture of the language and how it is
used. Sadly, this talk won't be *Chalk&Talk*, and a more conventional slidedeck will be used.
If tempted, I may do live programming.

> The protocols that describe the interactions between IP Cores on
> System-on-a-Chip (SoC) architectures are well-documented. Describing
> not only the structural properties of the physical interfaces but also
> the behaviour of the emanating signals. However, there is a disconnect
> between the design of SoC architectures, their formal description, and
> the verification of their implementation in known hardware description
> languages.
>
> Within the Border Patrol project we are investigating how to capture
> and reason about the structural and behavioural properties of SoC
> architectures using state-of-the-art advances in programming language
> research. Namely, we are investigating using dependent types and
> session types to capture and reason about hardware communication at
> design and runtime.
>
> In this talk I will discuss my work in designing a dependent type-
> system and corresponding languages that captures and reasons about the
> topological structure of a System-on-a-Chip. These languages provide
> correct-by-construction guarantees over:
>
> + the physical structure of an interaction protocol;
> + the adherence of a component’s interface to a given protocol; and
> + the validity of the specified connections made between components.
>
> We provide these guarantees through the (ab)use of dependent types as
> presented in Idris; and abuse of parameterised monads to reason about
> resource usage.

Slides are not available.
