# MuQ

The MuQ project intends to develop a new computation model for quantum computing including the circuit-based model as well as analog quantum computing models.

## Overview

We present MuQ, the first functional programming language for second quantization. MuQ generalizes quantum computation models, including the circuit model and analog models, and captures the computational abstractions across a wide range of applications, such as user-level algorithms, compilation procedures, and target machine system descriptions. The key design principle of MuQ is a combined classical-quantum model of lattice-based Hamiltonian particle systems, describable in second quantization. A novel type system for MuQ is developed to crystalize different particle states in different particle systems. We prove the relevant meta-theoretic properties of the type system and demonstrate its efficacy in guiding the development of multiple applications and compilation techniques in different fields, such as circuit-based compilations, analog computing-based compilations (Trotterization), and physics-based particle transformations, e.g., Jordan-Wigner Transformations, all of which are naturally definable in MuQ.

## Content

The artifacts are in the three directories, and there are instructions in each directory.

* coq directory contains the coq definitions and proofs for theorems in the paper.

* interpreter directory contains the interpreter for the classical energy computation in 3.1.

* simulations contains the python files run on SimuQ.
