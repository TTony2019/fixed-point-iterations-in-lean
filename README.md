# Formalization of Fixpoint Iterations

We aim to formalize the following iteration methods:

1. Krasnosel'skiĭ--Mann iteration;
2. Halpern iteration.

## Main Results

The main results of this formalization can be found in the following files:

- **Krasnosel'skiĭ--Mann Iteration**: 
  - **Location**: `Algorithm/KM/KM.lean`
  - **Theorem**: `Groetsch_theorem`
  
- **Halpern Iteration**: 
  - **Location**: `Algorithm/Halpern/Halpern.lean`
  - **Theorem**: `halpern_convergence`  

## lean4 toolchain installation
The library uses mathlib4 as a dependency, command `lake exe cache get` can be used to fetch mathlib4 cache.

## lean version 
leanprover/lean4:v4.27.0-rc1