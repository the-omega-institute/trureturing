---
bibkey: aubrun2024completely
authors: Guillaume Aubrun, Kenneth R. Davidson, Alexander Müller-Hermes, Vern I. Paulsen and Mizanur Rahaman
year: 2024
title: "Completely bounded norms of k-positive maps"
doi: 10.1112/jlms.12936
url: https://doi.org/10.1112/jlms.12936
claim: "Theorem 3.7: d₁(M_n) = n, i.e. every unital positive map on M_n has completely bounded norm at most n; the proof uses the separability of the block operator with identity diagonal blocks and off-diagonal block x/n for every contraction x in M_m(M_n)."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks
license: citation-only
triage: anchor
---

## Verified locator

Source: https://doi.org/10.1112/jlms.12936

DOI: 10.1112/jlms.12936 (J. London Math. Soc. 109, e12936). Text read from
https://arxiv.org/abs/2401.12352v2, printed p. 9.

Theorem 3.7 reads:

> For every n ⩾ 2, we have d₁(M_n) = n.

Its proof reads in part:

> Fix an integer m ⩾ 1 and an element x ∈ M_m(M_n) such that ‖x‖ ⩽ 1. By [1, Corollary
> 8.4], the operator $\begin{pmatrix} I_m\otimes I_n & \tfrac1n x\\ \tfrac1n x^* & I_m\otimes I_n\end{pmatrix}\in M_{2m}(M_n)$
> is separable, i.e., is a positive combination of elements of the form y ⊗ z for
> y ∈ M⁺_{2m} and z ∈ M⁺_n.

Reference [1] is T. Ando, *Cones and norms in the tensor product of matrix spaces*, Linear
Algebra Appl. 379 (2004), 3–41 (not read). By the duality between separable and
block-positive matrices, Theorem 3.7 is equivalent to the bound |Tr(WH)| ≤ m Tr W for
block-positive W on M_m ⊗ M_n and Hermitian contractions H, i.e. to the separability of
m I + H.
