---
bibkey: horodecki1999reduction
authors: Michał Horodecki and Paweł Horodecki
year: 1999
title: Reduction criterion of separability and limits for a class of protocols of entanglement distillation
doi: 10.1103/PhysRevA.59.4206
url: https://arxiv.org/abs/quant-ph/9708015v2
claim: "The reduction map relates positivity under partial transposition to the two Loewner inequalities between a bipartite density matrix and its marginal tensored with the identity."
strata_touched:
  - D5/S3/Quantum/Entanglement/Witness/PPTWeightedReduction
license: citation-only
triage: anchor
---

# The reduction criterion for bipartite probes

For a bipartite positive trace-one matrix, write b for its marginal on
the second factor. Positivity under partial transposition implies
ρ ≤ I ⊗ b. The reduction map composed with transpose is a sum
of congruences by antisymmetric matrix units. The Lean proof reuses that
finite identity on the first factor.

When b has positive eigenvalues r_i, the same inequality bounds the
weighted squared Hilbert–Schmidt norm of the probe by one. An identity
input direction bounds the trace of the residual positive realignment
Gram matrix from below. The resulting estimate depends on
the sum of reciprocal eigenvalues, so it also distinguishes probes with different
marginal spectra. Singh supplies the operational conditioning convention
and the separable benchmark. The weighted estimate comes from the
combined argument in the linked Lean module.

## Verified locator

[Pinned arXiv source](https://arxiv.org/abs/quant-ph/9708015v2).
[Published Physical Review A article](https://doi.org/10.1103/PhysRevA.59.4206).
[Singh's conditioning benchmark](https://arxiv.org/html/2605.19182v3#Thmdefinition5).
