# Hamiltonians and simple Simulator

Hamiltonians and Simulator are being translated from the following Python Jupyter notebook, also authored by JBG:


        20241215_Ising_Hamiltonians.ipynb

        20241224_Hamiltonian_Simulator.ipynb

Load necessary packages

        ghci> :set -package containers

        ghci> :set -package random

Load Simulator:

        ghci> :l H.Fn.Solver 

Run test functions:

        ghci> :l H.Fn.NumberPartition 
        ghci> testNumberPartitionH

        ghci> :l H.Fn.GraphPartition
        ghci> testGraphPartitionH