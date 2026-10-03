---
bibkey: debrota2020varieties
authors: John B. DeBrota; Christopher A. Fuchs; Blake C. Stacey
year: 2020
title: "The Varieties of Minimal Tomographically Complete Measurements"
doi: 10.1142/S0219749920400055
url: https://arxiv.org/abs/1812.08762v5
claim: "For an orthonormal basis of C^d, the orthocross MIC has elements E_alpha = Omega^(-1/2) Pi_alpha Omega^(-1/2), where Pi_alpha are the d^2 projectors onto |j>, (|j> + |k>)/sqrt(2) and (|j> + i|k>)/sqrt(2) (j < k) and Omega is their sum; its Gram matrix is G_ij = tr(E_i E_j); the authors conjecture that for any orthocross MIC the entries of G^(-1) are integers or half-integers; Conjecture 1: A rank-1 MIC in dimension 3 can have no more than 7 pairs of orthogonal elements."
strata_touched:
  - D5/S3/Quantum/Measurement/OrthocrossGramHalfInteger
  - D5/S3/Quantum/Measurement/QutritRankOneMicOrthogonalPairs
license: citation-only
triage: anchor
---

# The Varieties of Minimal Tomographically Complete Measurements

J. B. DeBrota, C. A. Fuchs and B. C. Stacey, arXiv:1812.08762 (v1 2018-12-20,
v5 2020-09-21); Int. J. Quantum Inf. 19 (2021) 2040005, published online
2020-10-27. Subject: quant-ph.

The paper studies minimal informationally complete measurements (MICs) and
their Gram matrices `[G]_{ij} := tr E_i E_j`. The orthocross MICs, introduced
by Caves, Fuchs and Schack for the quantum de Finetti theorem, are built from an
orthonormal basis `{|j⟩}`: the projectors `Γ_jj`,
`½(|j⟩ + |k⟩)(⟨j| + ⟨k|)` and `½(|j⟩ + i|k⟩)(⟨j| − i⟨k|)` for `j < k`, their
sum `Ω`, and `E_α := Ω^{−1/2} Π_α Ω^{−1/2}`. The paper computes `Ω` (diagonal
`d`, `½(1 − i)` above the diagonal) and its eigenvalues, and states:

> The following conjectures about orthocross MICs have been motivated by
> numerical investigations. We suspect that their proofs will be relatively
> straightforward, but so far they have eluded us. […] Conjecture. For any
> orthocross MIC, the entries in G^{−1} are integers or half-integers.

## Verified locator

- DOI: https://doi.org/10.1142/S0219749920400055 (metadata from Crossref; the
  journal text was not read).
- URL: https://arxiv.org/abs/1812.08762v5 (source retrieved 2026-09-30):
  `mic_facts.tex`, the definition of the Gram matrix in the introduction and
  the subsection on orthocross MICs (construction, `Ω`, and the two
  conjectures that close the subsection).

## Rank-one qutrit MICs and Conjecture 1

On printed pages 1-2 the paper defines the objects:

> Let ℋ_d be a d-dimensional complex Hilbert space, and let {E_i} be a set of
> positive semidefinite operators on that space which sum to the identity:
> ∑_(i=1)^N E_i = I.

> The set {E_i} is a positive-operator-valued measure (POVM), which is the
> mathematical representation of a measurement process in quantum theory.

> A POVM is said to be informationally complete (IC) if the operators {E_i}
> span ℒ(ℋ_d), the space of Hermitian operators on ℋ_d, and an IC POVM is
> said to be minimal if it contains exactly d² elements.

The Gram matrix is defined on printed page 2 by “[G]_{ij} := tr E_i E_j”.
On printed page 6, immediately after the seven-pair example, Conjecture 1 says:

> A rank-1 MIC in dimension 3 can have no more than 7 pairs of orthogonal elements.

The preceding example says:

> When multiplied by 1/3, the following is a rank-1 unbiased MIC in dimension
> 3 with 7 orthogonal pairs.

The conjecture itself imposes no unbiasedness restriction. Increasing pairs
`a < b` count distinct unordered pairs, excluding diagonal entries. In
dimension three minimality gives nine effects; informational completeness
means their real span is the Hermitian matrices. The new qutrit construction
has unequal traces and refutes this literal statement. It does not certify a
refutation restricted to unbiased MICs. The source locator is
https://arxiv.org/abs/1812.08762v5, `mic_facts.tex`, Conjecture 1 and the
preceding example (`7orthopairs`).
