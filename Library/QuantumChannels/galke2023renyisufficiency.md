---
bibkey: galke2023renyisufficiency
authors: N. Galke, L. van Luijk, H. Wilming
year: 2023
title: "Sufficiency of Rényi divergences"
doi: 10.48550/arXiv.2304.12989
url: https://arxiv.org/abs/2304.12989v6
claim: "Conjecture 22: equality of finite minimal quantum Rényi profiles on an interval with lower endpoint at least one half is equivalent to positive trace-preserving interconvertibility."
strata_touched:
  - D5/S3/QuantumChannels/RenyiSufficiency/BouquetFixedPoint
  - D5/S3/QuantumChannels/RenyiSufficiency/BouquetHolonomy
  - D5/S3/QuantumChannels/RenyiSufficiency/LikelihoodSpectrum
  - D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseClassification
  - D5/S3/QuantumChannels/RenyiSufficiency/PositiveInverseProjectionFrame
  - D5/S3/QuantumChannels/RenyiSufficiency/PositiveMapJordanDomain
  - D5/S3/QuantumChannels/RenyiSufficiency/RenyiSufficiencyRefutation
license: citation-only
triage: anchor
---

# Sufficiency of Rényi divergences

## Verified locator

DOI: 10.48550/arXiv.2304.12989

Source: https://arxiv.org/abs/2304.12989v6

Journal: IEEE Transactions on Information Theory 70(7), 5057–5076.
Journal DOI: 10.1109/TIT.2024.3376395.

## Source statement

Section 3.3, Conjecture 22, p. 17 of arXiv v6:

> Let (ρ₁, σ₁) and (ρ₂, σ₂) be pairs of density operators on quantum system S₁ and S₂. Let (a, b), ½ ≤ a < b, be any interval on which the minimal quantum Rényi divergences of both dichotomies are finite. Then the dichotomies are interconvertible via positive, trace-preserving maps if and only if they have the same minimal quantum Rényi divergences on this interval, i.e., (ρ₁, σ₁) ↔ (ρ₂, σ₂) ⇐⇒ Dᵐⁱⁿ_α(ρ₁, σ₁) = Dᵐⁱⁿ_α(ρ₂, σ₂) < ∞ ∀α ∈ (a, b).

Section 3.3, p. 16, Eq. (40):

> In the following, we therefore write

> (ρ₁, σ₁) ↔ᴾ (ρ₂, σ₂)

> if the two dichotomies can be interconverted using positive trace-preserving maps T, R.

The encoding requires a forward map and a reverse map carrying both states of each
dichotomy. Appendix E, p. 35, Eq. (105):

> The minimal quantum Rényi divergence (or sandwiched Rényi divergence) is given by

the sandwiched trace power displayed in the `Dmin` mirror.

> The limit α → 1 is the quantum relative entropy.

The value at alpha one is the Umegaki relative entropy; its finiteness
requires support inclusion.

## Scope

The five-dimensional bouquet dichotomies with perturbation 1/1000 and diagonal
reference state diag(1,2,3,4,5)/15 have equal finite minimal Rényi divergences on (2,3).
Their relative triangle orientations obstruct positive trace-preserving interconversion.
The proof uses Kadison equality, the Jordan domain, fixed-point rigidity and the
classification of unital positive inverse maps.

Theorem 13 and Lemma 24 supply the classical and commuting cases. Corollary 21
already excludes sufficiency of Petz and maximal quantum Rényi divergences.
Corollary 23 assumes Conjecture 22: its no-catalysis conclusion is not established
by the conjecture after this refutation, and is not refuted by the bouquet proof.
