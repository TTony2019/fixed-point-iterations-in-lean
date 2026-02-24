# Formalization of Fixed-point Algorithms

We formalize the following iteration methods:

1. Krasnosel'skiĭ--Mann iteration;
2. Halpern iteration.

A report is available on arXiv :

- Formalization of Two Fixed-Point Algorithms in Hilbert Spaces

   https://arxiv.org/pdf/2602.17064

## Main results

The main results of this formalization can be found in the following files:

- **Krasnosel'skiĭ--Mann Iteration**: 
  - **Location**: `Algorithm/KM/KM.lean`
  - **Theorem**: `Groetsch_theorem`
  
- **Halpern Iteration**: 
  - **Location**: `Algorithm/Halpern/Halpern.lean`
  - **Theorem**: `halpern_convergence`  

## Lean4 toolchain installation
The library uses mathlib4 as a dependency, command `lake exe cache get` can be used to fetch mathlib4 cache.

## Lean version 
leanprover/lean4:v4.27.0-rc1