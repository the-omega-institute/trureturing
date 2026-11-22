---
bibkey: galke2023renyisufficiency
authors: Niklas Galke, Lauritz van Luijk, and Henrik Wilming
year: 2024
title: Sufficiency of Rényi Divergences
doi: 10.1109/TIT.2024.3376395
url: https://arxiv.org/abs/2304.12989
claim: "For two commuting states, Appendix B groups equal likelihood ratios in the minimal sufficient decomposition, including a zero ratio when the comparison vanishes on a positive reference coordinate."
strata_touched:
  - D5/S3/Quantum/Recovery/DiagonalRecordCapacity
  - D5/S3/QuantumChannels/FibonacciBathRecordCapacity
license: citation-only
triage: anchor
---

# Likelihood classes in finite diagonal experiments

## Verified locator

Theorem 4 and Proposition 6 describe reversible statistical models and their sufficient decomposition.
Appendix B, equations (83)–(87), computes the blocks for two commuting states by grouping equal likelihood ratios.
The example includes a block with ratio zero.
[Primary text](https://arxiv.org/pdf/2304.12989v6#page=26)

## Formalization scope

The Lean development treats a family of diagonal comparisons supported on the reference.
Its statistic records the entire vector of likelihood ratios at each positive reference coordinate.
A channel preserving all fixed-reference Umegaki entropies admits a common recovery by the repository's support-aware Petz equality theorem.
The proof uses stationary finite kernels and a quantum measurement dimension bound, and constructs measure-and-prepare channels attaining that bound.
The thermal instance computes the ratios from the outgoing bath and its Gibbs preparation.
