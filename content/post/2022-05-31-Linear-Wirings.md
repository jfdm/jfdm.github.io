---
title: "Wiring Circuits is as easy as 0-1-Omega, or is it..."
tags: ["idris","dependent-types","border-patrol","tdvcs","hdl","systemverilog"]
date: 2022-05-31
---


In February 2022 I gave a PLInG talk about some work I have done investigating the application of quantitative type-systems to reasoning about wiring in netlists.
I am rehashing this talk for an internal seminar.

> Quantitative types allow us to reason more precisely about term
> usage in our programming languages. There are, however, other styles
> of language in which quantitative typing is beneficial: Hardware
> Description Languages (HDLs) for one. When wiring the components
> together it is important to ensure that there are no unused ports or
> dangling wires. Here the notion of usage is different to that found
> in general purpose languages. Although many linearity checks are
> detectable using static analysis tools such as Verilator, it is
> really interesting to investigate how we can use /fancy types/
> (specifically quantitative-type-theory \& dependent types) to make
> wire usage an intrinsic check within the type-system itself. With
> these /fancy types/ we can provide compile-time checks that all
> wires and ports have been used.
>
> Past work (unpublished) has seen me develop a novel orchestration
> language that uses fancy types to reason about module
> orchestration. Today, however, I want talk > about my work in
> /retrofitting/ a fancy-type system ontop of an existing HDL.
> Specifically, I have concentrated my efforts at the 'bottom' of the
> synthesis chain of SystemVerilog to type their netlists, a format
> from which hardware can be generated (fabless and fabbed). From this
> foundation, future work will be to promote my fancy-types: up the
> synthesis chain to a more comprehensive version of SystemVerilog; to
> new and better HDLs; or for similar application domains such
> algebraic circuits in Zero-Knowledge proofs.
>
> I will begin by introducing an unrestricted simply-typed netlist
> language and the design issues faced when capturing SystemVerilog's
> /interesting/ design choices. I will then describe how we can
> formally attest to the type-safety of our type-system. Lastly, I
> will detail how we can retrofit a linearly-wired type-system ontop
> of the same syntax.

This is joint work with [Wim Vanderbauwhede](https://twitter.com/wim_v12e).
