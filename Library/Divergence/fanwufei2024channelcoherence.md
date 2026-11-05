---
bibkey: fanwufei2024channelcoherence
authors: Jiaorui Fan; Zhaoqi Wu; Shao-Ming Fei
year: 2024
title: "Quantifying coherence of quantum channels based on the generalized α-z-relative Rényi entropy"
doi: 10.1007/s11128-024-04309-w
url: https://arxiv.org/abs/2506.10796v1
claim: "Section 3 conjectures C_{α,1}(φ) ≥ C̃_{α,1}(φ) for all quantum channels φ, with α ∈ (0,1) ∪ (1,2]."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/FanWuFeiChannelCoherenceDomination
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s11128-024-04309-w

Source: https://arxiv.org/abs/2506.10796v1

The source is Quantum Information Processing 23, article 100 (2024). The arXiv v1
text gives Eqs. (1)–(2) on page 2, Definition 2 and Eq. (7) on page 4,
Eq. (9) on page 6, Definition 4 and Eq. (10) on page 7, and the conjecture
in Section 3 on page 8.

## Source statements

Page 2, Eqs. (1)–(2): “D_{α,z}(ρ, σ) = (f_{α,z}(ρ, σ)^{1/α} − 1)/(α − 1)”,
with “f_{α,z}(ρ, σ) = Tr (σ^{(1−α)/2z} ρ^{α/z} σ^{(1−α)/2z})^z”.

Page 4, Definition 2, Eq. (7): “C_{α,z}(φ) = min_{φ̃ ∈ IC_AB} D_{α,z}(φ, φ̃)
= min_{M_φ̃ ∈ I} (f^{1/α}_{α,z}(M_φ, M_φ̃) − 1)/(α − 1)”.

Page 7, Definition 4, Eq. (10): “C̃_{α,z}(φ) = sup_ρ D_{α,z}(φ ∘ ∆_A(ρ),
∆_B ∘ φ(ρ)) … the supremum in Eq. (10) is taken over all quantum states.”

Page 8, Section 3: “From the examples in the next section and numerical results,
it is conjectured that C_{α,1}(φ) ≥ C̃_{α,1}(φ) holds for all quantum channels φ,
but we have not yet found a proof.”

## Mathematical interpretation

At z = 1 the matrix powers are the real continuous functional calculus. The Choi
matrix is normalized by the input dimension. Diagonal density matrices on the
product space are the feasible points of Eq. (7); the infimum formulation retains
that set. Eq. (10) ranges over every input density matrix. The parameter range
(0,1) ∪ (1,2] is the range of Eq. (8).

The qubit channel φ(X) = X₀₀ σ_{3/4} + X₁₁ σ_{1/2}, with
σ_t = [[1/2,t/2],[t/2,1/2]], contradicts the conjecture at α = 2.
Its Choi coherence is at most √(45/32) − 1, while its commutator coherence
is at least 1/4. No exact Choi coherence value or general parameter family
is asserted by this formalization.

## Literature boundary

Completeness of the prior-art screen is ASSUMED-UNVERIFIED. The preserved search
identified four citing works, an unresolved fifth Crossref citation, and two
unavailable full texts. The source's other channel examples and the extent of
surviving domination statements are outside the proved counterexample.
