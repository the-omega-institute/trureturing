---
bibkey: johnstonrussosikora2025antidistinguishability
authors: Nathaniel Johnston, Vincent Russo, Jamie Sikora
year: 2025
title: Tight bounds for antidistinguishability and circulant sets of pure quantum states
doi: 10.22331/q-2025-02-04-1622
url: https://arxiv.org/abs/2311.17047v2
claim: Theorem 5.1 gives a spectral sufficient condition for antidistinguishability; Corollary 5.4 gives an overlap bound whose tightness for n ≥ 5 is questioned in Section 6.
strata_touched:
  - D5/S3/Quantum/Measurement/AntidistinguishabilityGram
  - D5/S3/Quantum/Measurement/IncoherentCone
  - D5/S3/Quantum/Measurement/LocallyPositiveSpectrum
  - D5/S3/Quantum/Measurement/AntidistinguishabilitySpectrum
  - D5/S3/Quantum/Measurement/OverlapLowRankDistance
  - D5/S3/Quantum/Measurement/AntidistinguishabilityOverlapNonTight
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.22331/q-2025-02-04-1622

Source: https://arxiv.org/abs/2311.17047v2

The arXiv v2 record identifies this work as Quantum 9, 1622 (2025) and supplies the DOI above.

## Statements

Section 2.1, page 3: “The set of states is antidistinguishable if there exists a POVM such that ⟨ψi|Mi|ψi⟩ = 0 for all 0 ≤ i ≤ n − 1.” A POVM consists of positive semidefinite effects whose sum is the identity.

Theorem 5.1, page 12: “Let n ≥ 2 be an integer and let G ∈ Pos(ℂⁿ) be the Gram matrix of a set S of n pure states, and let λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ₋₁ be the eigenvalues of G.” The displayed condition is

$$
\sqrt{\lambda_0}\leq\sum_{j=1}^{n-1}\sqrt{\lambda_j}.
$$

It implies that S is antidistinguishable, and is necessary for circulant G.

Corollary 5.4, page 15: “Let n ≥ 2 be an integer and let S = {|ψ₀⟩, |ψ₁⟩, . . . , |ψₙ₋₁⟩}. If”

$$
|\langle\psi_i|\psi_j\rangle|\leq\frac{1}{\sqrt{2}}\sqrt{\frac{n-2}{n-1}}
\quad\text{for all }0\leq i\ne j\leq n-1,
$$

“then S is antidistinguishable.”

Section 6, page 17: “We still do not know whether or not Corollary 5.4 is tight when n ≥ 5.”

## Encoding and boundary

The formal states have type `Fin n → EuclideanSpace ℂ (Fin d)`. A finite family of positive semidefinite matrices summing to the identity supplies the POVM. The Gram matrix is the existing `Matrix.gram ℂ` construction. The squared overlap cap is `(n - 2) / (2 * (n - 1))`, with subtraction in ℝ.

The repository-derived improvement uses δₙ = (n − 9)/(16n(n − 1)(n − 3)) for every n ≥ 10. It does not decide the source's cases n = 5,…,9 or alter the source's circulant characterization and sharp Frobenius bound.
