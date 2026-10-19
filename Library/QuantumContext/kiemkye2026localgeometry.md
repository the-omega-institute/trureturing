---
bibkey: kiemkye2026localgeometry
authors: Young-Hoon Kiem; Seung-Hyeok Kye
year: 2026
title: "Local geometry for Schmidt number witnesses"
doi: 10.48550/arXiv.2608.14199
url: https://arxiv.org/abs/2608.14199v1
claim: "Sections 2, 3 and 5 define local distinguishability and the trace-one blockpositive sets, and conjecture local distinguishability of adjacent blockpositive sets around every boundary projection state."
strata_touched:
  - D5/S3/Quantum/Entanglement/LocalDistinguishability/KiemKyeLocalDistinguishability
license: citation-only
triage: anchor
---

# Kiem and Kye, local geometry for Schmidt number witnesses

## Verified locator

DOI: 10.48550/arXiv.2608.14199

Source: https://arxiv.org/abs/2608.14199v1

## Source statements

Section 2, page 6: "Suppose that closed convex sets C and D with the inclusion C ⊃ D share a boundary point x₀. We say that C ⊃ D is locally distinguishable around x₀ if the set N ∩ (C∖D) is nonempty for every neighborhood N of x₀."

Section 3, page 7: "A Hermitian matrix W ∈ M_m ⊗ M_n is called k-blockpositive if ⟨ξ|W|ξ⟩ ≥ 0 for every |ξ⟩ with SR |ξ⟩ ≤ k."

Section 5, page 12: "For non-generic cases, we cannot show the existence of Schmidt number witnesses around ϱ_{E⊥} by the method in this paper. Nevertheless, we conjecture that the inclusion BP_ℓ ⊋ BP_{ℓ+1} is locally distinguishable around ϱ_{E⊥} for ℓ ≥ k, whenever ϱ_{E⊥} is on the boundary of the convex set BP_k."

## Mathematical scope

The affine space H consists of trace-one Hermitian matrices. The set BP_k restricts the quadratic-form tests to coefficient matrices of rank at most k. The state ϱ_{E⊥} is the orthogonal projection onto E⊥ divided by its complex dimension. The adjacent inclusions have 1 ≤ k ≤ ℓ < min(m,n).

The repository proof uses rank-one perturbations to raise the coefficient-matrix rank, normalized compressions to move a kernel, and a compact overlap bound to construct nearby matrices in BP_ℓ ∖ BP_{ℓ+1}. It includes non-generic subspaces. The converse characterization for arbitrary density matrices and quantitative convergence rates remain open here.

Literature completeness is ASSUMED-UNVERIFIED. Sections 3–4 prove generic cases; the assertion quoted from Section 5 is the external question addressed by the repository proof.
