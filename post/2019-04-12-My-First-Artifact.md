---
title: Provisioning My First Artifact.
tags: paper,advice,repoducible,artifact
...


A up-and-coming trend in *Programming Languages* (PL) conferences is that of *reproducible science*.
If you ran experiments, let other reproduce them; if you build a system, let other people play with it; if you (and you should) mechanised your proofs; let others rerun said proofs!
Most research projects will have some artefact of one kind or another be it a system, a proof, or experiment.
Many conferences are now starting to introduce [artifact evaluations](https://www.artifact-eval.org/) as a separate track to help ensure an accepted paper's artefact is reproducible [^1].


Last year, Simon Fowler [talked about their own experiences](http://simonjf.com/2018/12/14/popl19-aec.html) with artifact evaluations, and gave some interesting thoughts about the process.

In this post I will describe my experiences fashioning an artifact for submission to [ECOOP '19](https://2019.ecoop.org/track/ecoop-2019-artifacts).
I will try to remember to write a separate post, post evaluation rounds.

## The Artifact

For [ECOOP '19](https://2019.ecoop.org/track/ecoop-2019-papers) we have presented a *Typing Discipline for Hardware Interfaces*, the details about this approach will come later in June when the final camera ready copies are required.
The core contribution we are providing is a more formal way to describe an *Abstract Interface Definition* for a hardware *module* and ensuring that the interfaces on a module adhere to a given abstract definition.
We utilise dependent typing and notions of projection from Session Types to provide our guarantees.
We further demonstrated our model's efficacy on three case studies of existing hardware interfaces, and also on a small self-contained exemplar description.

We have developed our formalisms using [Idris](https://www.idris-lang.org) a language that blurs the line between general purpose functional programming with dependent types, and theorem proving [^2].
Our implementation in Idris is thus the artifact to be evaluated.

## What is required?

The evaluation committee has provided guidelines for what they expect to receive.
Which we repeat here:

+ An abstract that briefly describes the artifact.
+ A PDF file that describes the artifact in detail and provides instructions for using it.
+ A URL for downloading the artifact.
+ A PDF file of the most recent version of the accepted paper.

They also provide guidelines for *packaging* the artifact itself.
They can be summarised as:

1. It should be accessible, and facilitate quick investigative progress.
2. Provide material that describe how to use the artifact for example: tutorials.
3. Aim to avoid software dependency issues!
4. The artifact must be available in a single self-contained archive.
5. Use widely available open document[^3] and data formats.

## Software Dependency Issue Avoidance

We are providing a software artefact, and with software comes [dependency hell](https://en.wikipedia.org/wiki/Dependency_hell).
The best way to avoid such issues is to provide a coherent means to obtain the required software.
Traditionally, within Software Engineering practises this can be achieved through: **Excellent installation instructions**.

If one is fortunate then your software dependencies will be packaged, and easily available to install on people's computers.
We are not all fortunate children, and we all know how good users are at following instructions, and research software is not always easy to install when it depends on non-mainstream tooling.

A promising trend is to use a [container based approach](https://en.wikipedia.org/wiki/OS-level_virtualisation).
In fact in [Simon's post](http://simonjf.com/2018/12/14/popl19-aec.html) they mention their use of Docker, and the trials and tribulations of its use.
While this is an interesting way to ensure consistent build environments, and colleagues have attested to this with their own projects, I am not yet sold on its use for reproducible experiments.

Rather than go down this route, my thinking is to present a self-contained virtual machine that has the required components pre-installed.
This allows me to provide a working snapshot of the environment in which my artifact can run as it stands now, and minimise issues for evaluation.
This also helps with [software conservation](https://en.wikipedia.org/wiki/Conservation_(ethic)) in that I am preserving the natural habitat in which my artefact will run, and that this environment might not be around forever!

Further, spurred on by Simon's own conclusion's I will also provide the code online when submitting the camera ready version.

## My Setup

My approach to artefact creation is thus:

> I will provision a virtual machine that contains a working Idris installation, together with the artefact to be evaluated.

I will detail these steps below.

### Virtual Box

[Virtual Box](https://www.virtualbox.org/) is a free and open source tool for working with Virtual Machines.
However, Virtual Box is primarily a GUI based tool with minimal command line options.
Moreover it requires that you *manually* organise your machines.

### Vagrant

[Vagrant](https://www.vagrantup.com/) is a tool for helping to automate Virtual Machine instances.
The company behind the tool states:

> Vagrant is a tool for building and managing virtual machine environments in a single workflow. With an easy-to-use workflow and focus on automation, Vagrant lowers development environment setup time, increases production parity, and makes the "works on my machine" excuse a relic of the pas

With Vagrant the idea is that one can launch and interact with a virtual machine as simply as:

```{.sh}
vagrant init hashicorp/precise64

vagrant up Bringing machine 'default' up with 'virtualbox' provider...
==> default: Importing base box 'hashicorp/precise64'...
==> default: Forwarding ports...
default: 22 (guest) => 2222 (host) (adapter 1)
==> default: Waiting for machine to boot...

vagrant ssh vagrant@precise64:~$ _
```

I like this idea, as it simplies the interaction.
Further, Vagrant works with Virtual Box and allows you to use existing virtual box images.

However, we need to construct compatible images.
Fortunately, the people behind Vagrant has just the tool.


### Packer

[Packer](https://www.packer.io/) is a tool for automating the construction of execution environments for software.
Think of it as the Swiss Army knife of environment provision.
So rather than handcraft a virtual machine, I used Packer to make the virtual machine image generation itself reproducible and mechanised.

My use of Packer was two-fold:

1. A packer setup to generate a virtual machine that presents an execution environment for program's that compile against Idris-stable---1.3.1 as of 2019-04-19.
2. A packer setup that uses this execution environment for provisioning a copy of the virtual machine with a research artefact.

Overall, this was a good setup as it meant that the execution environment can be easily reused for other artifacts.

I decided to base the execution environment on Ubuntu 18.04 LTS Server, as I am most familiar with this family of operating systems and I am going to ssh into resulting virtual machine image.
To install Idris, required installing Haskell.
So while virtual machine creation and OS installation was relatively quick, obtaining and installing Idris was **slow**.
The turnaround time from start to finish was approx 40 minutes.
This meant that if I discovered a mistake (and I did many times) in the resulting machine, it took a while to discover.
My mistakes included:

0. not getting Idris to install correctly due to dependency issues;
1. not including enough virtual memory;
2. setting wrong permissions when installing software;
3. changing permissions but not to a correct setting;
4. Generally 2 and 3;

Other than that the process was straight forward.

The turnaround time for step two was quicker, around five minutes.
It consisted of copying the virtual machine across, copying some files on and that's it.

You can find my packer setup for Idris-Stable online:

<https://github.com/jfdm/packer-idris>.

This is a first draft of the configuration, and I need to prune and shrink the required virtual machine once I have more motivation to do so.

## Submission

In the end, I submitted:

+ A vagrant box.
+ Detailed instructions on how to work with Vagrant, including changing the configuration[^4].
+ A link to the submission archive.
+ HTML marked-up versions of the source.
+ Generated IdrisDoc
+ Copy of the source code, together with dependencies.

We will see how it goes.

## Resources

The main resource I used for using Packer came from this link.

<https://www.serverlab.ca/tutorials/dev-ops/automation/how-to-use-packer-to-create-ubuntu-18-04-vagrant-boxes/>


The rest of the information I was able to learn from each software's of documentation.

[^1]: Like well marked appendicies this process does not affect the final result of paper acceptance, and normally occurs after the final paper notification.

[^2]: Idris is a cool language, I suggest looking into it and other languages like Agda.

[^3]: This might mean Org-Mode is of the table :-(

[^4]: I don't use the default vagrant username/password it is customised. This means I cannot use vagrant out-of-the-box and must ask uses to configure the vagrant settings with custom information.
