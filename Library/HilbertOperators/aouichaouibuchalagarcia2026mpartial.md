---
bibkey: aouichaouibuchalagarcia2026mpartial
authors: Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia
year: 2026
title: 'On m-partial isometries: spectra, weighted shifts, and similarity'
doi: 10.48550/arXiv.2606.12865
url: https://arxiv.org/abs/2606.12865v1
claim: 'Question 6 asks whether the fixed operator 2T∗ − T∗²T is the Moore–Penrose inverse of every 2-partial isometry T for some inner product.'
strata_touched:
  - D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2606.12865

Source: https://arxiv.org/abs/2606.12865v1

## Source statements

Question 6, page 17: “If T is a 2-partial isometry, is 2T∗ − T∗²T the Moore–Penrose inverse of T with respect to some inner product?”

Section 2, page 2: “More generally, T is an m-partial isometry if T βₘ(T) = 0; it is strict if it is not an (m − 1)-partial isometry.” The operator definition preceding equation (2.1), page 2, defines βₘ(T) := Σₖ₌₀ᵐ (−1)ᵐ⁻ᵏ binom(m,k) T*ᵏTᵏ for integer m ≥ 1.

Section 6, page 17: “so S = 2T∗ − T∗²T is a generalized inverse for T and ST is the orthogonal projection onto R(T*).” The adjoints in S refer to the original Hilbert space. Question 6 asks for one new positive definite complex inner product making both TS and ST symmetric, in addition to TST = T and STS = S. It does not allow two independently chosen weights.

Lemma 2.8, page 4, proves TST = T and STS = S for S := Σₖ₌₁ᵐ (−1)ᵏ⁻¹ binom(m,k) T*ᵏTᵏ⁻¹. The common-metric obstruction does not change those two identities.
