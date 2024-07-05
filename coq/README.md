# MuQ

The MuQ project intends to develop a new computation model for quantum computing including the circuit-based model as well as analog quantum computing models.

## Overview

We present MuQ, the first functional programming language for second quantization. MuQ generalizes quantum computation models, including the circuit model and analog models, and captures the computational abstractions across a wide range of applications, such as user-level algorithms, compilation procedures, and target machine system descriptions. The key design principle of MuQ is a combined classical-quantum model of lattice-based Hamiltonian particle systems, describable in second quantization. A novel type system for MuQ is developed to crystalize different particle states in different particle systems. We prove the relevant meta-theoretic properties of the type system and demonstrate its efficacy in guiding the development of multiple applications and compilation techniques in different fields, such as circuit-based compilations, analog computing-based compilations (Trotterization), and physics-based particle transformations, e.g., Jordan-Wigner Transformations, all of which are naturally definable in MuQ.

## Setup

To compile MuQ, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.13**.

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "qnp"
opam switch create qnp 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We require Coq version >= 8.12. We have tested compilation with 8.12.2, 8.13.2, and 8.14.0.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running MuQ

Run `make` in the top-level directory to compile our Coq proofs.

## Directory Contents

* MuQSyntax.v - The MuQ language syntax.
* MuQSem.v - The MuQ language semantics.
* MuQType.v - The MuQ Type system.
* MuQTypeProof.v - The MuQ Type system Soundness Proof.

