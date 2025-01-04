# Hamiltonians

## /notebooks

Hamiltonians and Simulator are being translated from the following Python Jupyter notebook, also authored by JBG:


        20241215_Ising_Hamiltonians.ipynb

        20241224_Hamiltonian_Simulator.ipynb

## /Imp (imparative)

Pretty much a direct Haskell translation of the Python code in the notebooks. "Imp" is short for "imperative", it's not imperative, but the pattern more or less "feels" that way.

## /Fn (functional)

An iteration of the `/Imp` Solver, "Fn" for functional, but in a similar functional pipeline pattern of what is in DSL. Meaning:

`minimize` ◦ `solve_` ◦ `generateSpins`

However, only really works equally well for both classical and quantum versions, where the Hamiltonian in the quantum case results in a diagonalized matrix.

## /Trav (traverable)

This is a take on the generate choices pattern also in `/DSL`. Ideally no big departure here.

`minimize` ◦ `solve_` ◦ `generateChoices`

In all cases `solve_` means either `solveClassical` or `solveQuantum`.

