---
bibkey: gurvitsbarnum2002largest
authors: Leonid Gurvits and Howard Barnum
year: 2002
title: "Largest separable balls around the maximally mixed bipartite quantum state"
doi: 10.1103/PhysRevA.66.062311
url: https://doi.org/10.1103/PhysRevA.66.062311
claim: "Theorem 1: I + Δ is separable for every Hermitian Δ with Frobenius norm at most one. Proposition 1: the block matrix with identity diagonal blocks and off-diagonal block X is separable when the operator norm of X is at most one."
strata_touched:
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall
  - D5/S3/Quantum/Entanglement/AbsoluteSeparability/ContractionBlocks
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1103/PhysRevA.66.062311 (Phys. Rev. A 66, 062311). Text read from
https://arxiv.org/abs/quant-ph/0204159v2.

Theorem 1 (printed p. 4) reads:

> The matrix I + ∆ is separable for all hermitian ∆ with ||∆||₂ ≤ 1.

Proposition 1 (printed p. 2) reads:

> If ||X|| ≤ 1, the block matrix $\begin{pmatrix} I & X \\ X^\dagger & I\end{pmatrix}$ is separable.

Corollary 2 (scaling, printed p. 5) reads:

> Let A be an (unnormalized) density matrix of a bipartite system with total dimension
> d = NM and λ = (λ₁,...,λ_d) be the vector of eigenvalues of A. If
> S(λ) =: d − ||λ||₁²/||λ||₂² ≤ 1 then A is separable.

Its proof writes A = b(I + ∆) with b > 0 and ||∆||₂² ≤ 1. The paper proves Theorem 1
through positive unital maps and the separability criterion by positive maps.

S. J. Szarek, E. Werner and K. Życzkowski, *Geometry of sets of quantum maps: a generic
positive map acting on a high-dimensional system is not completely positive*, J. Math. Phys.
49, 032113 (2008), https://doi.org/10.1063/1.2841325 (text read from
https://arxiv.org/abs/0710.1571v2, printed p. 18), state the dual inequality and ask for a
direct proof:

> If M = (M_jk) is a block-positive matrix, then Tr (M²) ≤ (Tr M)². It would be nice to
> have a simple direct proof of the above inequality, as it would yield (via Lemma 1 and
> (21)) an alternate derivation of the result from [13] concerning the in-radius of the set
> of separable states in the bivariate case.
