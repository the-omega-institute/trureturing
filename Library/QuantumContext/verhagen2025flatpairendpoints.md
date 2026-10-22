---
bibkey: verhagen2025flatpairendpoints
authors: Frits Verhagen; Marco Tomamichel; Erkka Haapasalo
year: 2026
title: "Conditions for Large-Sample Majorization of Pairs of Flat States in Terms of α-z Relative Entropies"
doi: 10.1007/s00220-026-05675-5
url: https://arxiv.org/abs/2507.07520v3
claim: "Remark 15 suspects that the additional endpoint and negative tropical homomorphisms on everywhere overlapping flat pairs are not monotone."
strata_touched:
  - D5/S3/QuantumChannels/FlatPairEndpointHomomorphisms
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.1007/s00220-026-05675-5

Source: https://arxiv.org/abs/2507.07520v3

The quotations below are from version 3, pp. 9–10 and 16–21, in Sections 4.1 and 4.3.

## Flat pairs and the question

Equation (31) writes the block matrices as “A = ⊕ᵢ |αᵢ⟩⟨αᵢ|, B = ⊕ᵢ |βᵢ⟩⟨βᵢ|”. Equations (33)–(34), p. 9: “Also, we define the set of everywhere overlapping pairs Vₑ.ₒ. ⊊ Vₘ.ᵣ. to be those (A, B) ∈ Vₘ.ᵣ. such that, for any i ∈ [n], we have either ⟨αᵢ|βᵢ⟩ ≠ 0 or |αᵢ⟩ = 0 = |βᵢ⟩.” The matrices are compared by one quantum channel acting on both members of the pair: “(A, B) ≽ (C, D) if and only if there exists a quantum channel 𝒞 … such that 𝒞(A) = C and 𝒞(B) = D” (pp. 9–10).

Equation (37), p. 10, specifies that “the vector |αᵢ⟩ is normalized when pᵢ > 0 and equal to the zero vector when pᵢ = 0, and similarly for the |βᵢ⟩, qᵢ.” Equation (84), p. 16, is “Φ_{α,z}(A, B) := Σᵢ (pᵢ)^α (qᵢ)^{1−α} |⟨αᵢ|βᵢ⟩|^{2z}”; Eq. (85), p. 17, is “Φ^𝕋_z(A, B) := max_{i=1,…,n} |⟨αᵢ|βᵢ⟩|^{2z}”.

Remark 15, p. 21:

> Namely, it is still an open question whether the homomorphisms for 𝕂 = ℝ₊ or ℝ₊ᵒᵖ that have the same form as (84), but with parameters α = 0, z < 1, or α = 1, z < 1, are monotone or not. The same question of monotonicity can also be asked for the homomorphisms for 𝕂 = 𝕋ℝ₊ that are similar to (85), but with z < 0.

> We suspect that these additional homomorphisms are in fact not monotone either, since they correspond to parameters α, z for which the α-z relative entropy is known not to satisfy DPI for general pairs of quantum states (with some conditions on the support).

The endpoint statement excludes z = 0: the source identifies the degenerate trace homomorphisms separately. The tropical opposite order and monotone derivations are separate questions.

## Encoding

A finite family of block dimensions and complex vectors represents each pair. Each block matrix uses `Matrix.vecMulVec`, and the direct sum uses `Matrix.blockDiagonal'`. The weights are the real parts of the self dot products; normalized squared overlaps divide `Complex.normSq` of the cross dot product by the product of the weights. Zero blocks contribute zero to the sum and to the maximum initialized at zero.

The new proof retains the two filter outcomes in orthogonal blocks, applies strict Jensen inequalities, and uses erasure for the other order. Swapping the pair gives the other endpoint. It addresses all real parameters in the stated ranges.
