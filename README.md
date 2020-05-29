# The Duality of Subtyping (Artifact)

Abstract
--------
This artifact contains the Coq formulation of Duotyping associated with the paper "The Duality of
Subtyping". This document explains how to run the Coq formulations. It also explains the Coq
files briefly. Artifact can either be compiled in the pre-built docker image with all the dependencies
installed or it could be built from the scratch.

Docker Image
------------

This section explains how to pull the docker image of artifact from docker repo and use it.
Run the following commands one by one in terminal:

1. $ docker pull baberrehman/duotyping
2. $ docker run -it baberrehman/duotyping
3. $ eval $(opam env)

The artifact is located in /home/coq/coq-duotyping/coq/ directory.

There are two folders in the artifact, with make file in each:

1. MonoTyping → contains traditional subtyping formulation
2. DuoTyping → contains our duotyping formulation

Go to each folder and run make:

1. $ cd /home/coq/coq-duotyping/coq/DuoTyping
2. $ eval $(opam env)
3. $ make

1. $ cd /home/coq/coq-duotyping/coq/MonoTyping
2. $ eval $(opam env)
3. $ make


Build from Scratch
------------------

This section explains how to build the artifact from scratch

### Preprequisites
We tested all the Coq files using Coq version 8.7.0. Please use same version for the sake
of consistency. We recommend installing Coq using the opam package installer. Coq TLC
library is also required to compile the code. TLC library can also be installed using the
opam package installer. User should be able to run each file individually using Coqide if
these dependencies are installed. Refer to this link for more information and installation
steps: https://coq.inria.fr/opam-using.html

### Getting the files
Use the following commands to clone our git repo. Please note that **$** symbol is not a part of command:

$ git clone https://github.com/baberrehman/coq-duotyping.git

You should be able to see all the Coq files inside folder **coq** after cloning the repo. Alternatively you can
download the zip file from repo and you should be able to see all the Coq files after unzipping it.

You can also find a copy of our ECOOP'20 paper (The Duality of Subtyping) in **docs** folder.

Coq files
---------
This section explains all the Coq files of our Duotyping systems and the traditional subtyping
systems that we formalized. A table below shows the correspondance of Coq files and
the respective systems. For example, one can find the Coq code for the system λ <: in file
Monotyping/STLCSub.v (we consider unzipped suplements directory as reference point).
We have algorithmic and the declerative formulation for all the Duotyping systems.


| Name   | Description                                                                  | Coq File                          |
|--------|------------------------------------------------------------------------------|-----------------------------------|
| λ<:    | STLC with subtyping                                                          | Monotyping/STLCSub.v              |
| λ♦     | STLC with Duotyping (Algorithmic)                                            | GStlc.v                           |
| λ♦     | STLC with Duotyping (Declerative)                                            | GStlcExtra.v                      |
| λ<:∧∨  | STLC with subtyping, union and intersection types                            | Monotyping/STLCSubUnionInter.v    |
| λ♦∧∨   | STLC with Duotyping, union and intersection types (Algorithmic)              | GUnionInter.v                     |
| λ♦∧∨   | STLC with Duotyping, union and intersection types (Declerative)              | GUnionInterExtra.v                |
| Fk<:   | System F<: kernel                                                            | Monotyping/FSubKernal.v           |
| Fk♦    | System F<: kernel with Duotyping (Algorithmic)                               | GFSubKernel.v                     |
| Fk♦    | System F<: kernel with Duotyping (Declerative)                               | GFSubKernelExtra.v                |
| Fk<:∧∨ | System F<: kernel union and intersection types                               | Monotyping/FSubKernalUnionInter.v |
| Fk♦∧∨  | System F<: kernel with Duotyping, union and intersection types (Algorithmic) | GFSubKernelUnionInter.v           |
| Fk♦∧∨  | System F<: kernel with Duotyping, union and intersection types (Declerative) | GFSubKernelUnionInterExtra.v      |
| FF<:   | System full F<:                                                              | Monotyping/FSub.v                 |
| FF♦    | System full F<: with Duotyping (Algorithmic)                                 | GFSubFull.v                       |
| FF♦    | System full F<: with Duotyping (Declerative)                                 | GFSubFullExtra.v                  |