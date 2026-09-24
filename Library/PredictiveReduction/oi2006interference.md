---
bibkey: oi2006interference
authors: Daniel K. L. Oi; Johan Aberg
year: 2006
title: Fidelity and Coherence Measures from Interference
doi: 10.1103/PhysRevLett.97.220404
url: https://arxiv.org/abs/quant-ph/0603157
claim: Under the paper's allowed subspace-preserving operations, maximal retained two-path coherence equals root Uhlmann fidelity; more restricted local gluings have a different optimum.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Pairwise coherence is established prior art

## Verified source and scope

The arXiv bibliographic record and the four-page PDF were read. Equation (6) and its Stinespring discussion identify the maximum subspace-preserving coherence with the trace norm of the product of state square roots. The source distinguishes this operation class from local subspace-preserving gluings. Root fidelity is used, without squaring it.

## Use in the thermal-dynamical recovery volume

The thermal recovery extension uses this existing two-state mechanism for fixed conditional Gibbs states. Its population-preserving channel is specified independently by diagonal calibration and a Stinespring isometry. The pairwise fidelity ceiling is background, not a new theorem or an open-problem resolution.

The research target is the joint realizability of all pairwise optima by one channel, with cycle constraints and separately imposed Hamiltonian covariance. The source's pairwise theorem alone does not establish those joint optima. No content of the existing Lean observable-orbit declaration proves the new recovery bounds. No claim of experimental implementation, free thermal-operation cost or global novelty is made.
