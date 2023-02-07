---
title: "Efficient and Effective Provisioning of Virtual Machines for Artefact Evaluation"
tags: ["idris","artifact","reproducible","nix"]
date: 2023-01-05
---


[I have written about artifact provisioning before.](https://jfdm.github.io/post/2019-04-12-My-First-Artifact.html)
Even though I have yet to publish in recent years, I have been keeping my artifact provision game up.

This is because some conferences (ECOOP '23) are now requiring artefacts at time of (well a week later) of submission.
This is not a bad approach __per se__ as it contributes towards reproducible results, in some form.
Moreover, when reviewing artefacts in the past, I have had to download GBs worth of VM for what is essentially a very small program, or download GBs of data on top of that (this was related to external propriety software).

While one can think about what a artifact should demonstrate from a paper and how, in general I see two approaches that artefact evaluation committees (of which I recently co-chaired APLAS'22 AEC) tend to recommend for packaging up results:

1. containers; and
2. virtual machines.

My intuition tells me that container's are more of a devops/production oriented approach to reproducing the working environment locally for deployment today, and that virtual machines are the librarian/conservancy approach to reproducing the working environment of the time.

There are other aspects of artefact presentation (documentation and bundling) that I am keen on that I won't bore people with here.

Moreso, and the point of this post is to highlight my current approach to artefact provisioning based on virtual machines.

Of note, my approach doesn't apply to all circumstances.
If one searches one can find discussions/concerns over reproducing results that have been run on bare metal, or with very specific setups (cf. Google Borg, Amazon Dynamo et cetera).
This is a larger discussion various communities should have.

## Use Virtual Machines and automate their provisioning.

I use HashiCorps packer to provision Virtual Box machines. [I have written about this before](https://jfdm.github.io/post/2019-04-12-My-First-Artifact.html).
The main thing to mention is that I have adjusted the scripts to be a bit more flexible.
A mistake recently was not giving each build a unique directory (the output dir was deleted when running packer with `-force`).


## Use a Minimal OS for small footprint.

Since my ECOOP artefacts from ECOOP'20, I use Alpine linux for my base virtual machine.
This leaves you with a starting box that is approx. 200MB in size.
Which is better than using stock Ubuntu LTS which is minimally 2GB in size.
An order of magnitude in difference when downloading/uploading on a home network!

Further the provisioning time is much quicker.
I can go from an empty directory to a minimal box in the time it takes to brew a mokka pot (approx. 2-3 minutes), or realistically with today's gas prices a french press....
When I used Ubuntu LTS it was, IIRC, 15-20 minutes.
An order of magnitude in difference when addressing problems in scripts.


## The New Thing: Use a Universal Package Manager when necessary.

Recently when provisioning a recent artefact for submission, I was having to install Idris2 by hand.
This takes time, and for Idris1 this was around, IIRC, 20 minutes to install the required dependencies, and compile/build.
For Idris2, it is much quicker.

Recently, I was pleased to discover that Alpine Linux has Idris2 in it's own repository.
This makes provisioning even quicker!
Sadly Alpine didn't have another tool I required: Verilator.
I tried compiling it by hand, and this took around 40 minutes, and a few tries when realising that I had run out of virtual diskspace, and dependencies.
To resolve these issues, I ended up introducing `nix` to my setup.
Still wanting to be minimal, I refused to use NixOS (concerns about final box size), and I now recommend having an Alpine+NixPkgs solution.

Using Nix I was able to provision my artefacts (from an empty directory) in around 10-15 minutes.

With the resulting images from recent artefacts being around 500mb and 600MB.
Which is still better than 5GB.

## It's online.

You can find my packer scripts online: https://github.com/jfdm/packer-idris/

Thanks to gallais for addressing some niggles, and introducing a CI.
