/- GID: D5/S3/Resource/LogDet/KoteljanskiiPrincipalBlocks
   generality: G
   mirror-B: D5/B/S3/Resource/LogDet/KoteljanskiiPrincipalBlocks
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Koteljanskii determinant and logarithm inequalities for Hermitian principal blocks. -/

import D5.S3.Resource.LogDet.LogDetInformationSubmodularity
import Mathlib.Data.Finset.Basic

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Resource.LogDet.KoteljanskiiPrincipalBlocks

private theorem det_mono {α : Type*} [Fintype α] [DecidableEq α]
    {P Q : Matrix α α ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hPQ : (Q - P).PosSemidef) : P.det.re ≤ Q.det.re := by
  sorry

private theorem schur_factor {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hH : H.PosDef) :
    let P := H.submatrix Sum.inl Sum.inl
    let X := H.submatrix Sum.inl Sum.inr
    let Q := H.submatrix Sum.inr Sum.inr
    (Q - Xᴴ * P⁻¹ * X).PosDef ∧
      H.det.re = P.det.re * (Q - Xᴴ * P⁻¹ * X).det.re := by
  sorry

private theorem fischer {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hH : H.PosDef) :
    H.det.re ≤ (H.submatrix Sum.inl Sum.inl).det.re *
      (H.submatrix Sum.inr Sum.inr).det.re := by
  sorry

private theorem block_koteljanskii {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (H : Matrix (β ⊕ (α ⊕ γ)) (β ⊕ (α ⊕ γ)) ℂ) (hH : H.PosDef) :
    H.det.re * (H.submatrix Sum.inl Sum.inl).det.re ≤
      (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det.re *
        (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det.re := by
  sorry

private theorem principal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  sorry

/-- Koteljanskii's inequality, with determinants read as positive real numbers. -/
theorem koteljanskii {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  exact principal_product H hH A B C hAB hAC hBC

/-- The logarithmic principal-block inequality, including empty blocks. -/
theorem result {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    Real.log (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      Real.log (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re +
        Real.log (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  have h := koteljanskii H hH A B C hAB hAC hBC
  have hp (X : Finset ι) :
      0 < (H.submatrix (Subtype.val : ↥X → ι) Subtype.val).det.re :=
    (hH.submatrix Subtype.val_injective).det_pos.1
  have hl := Real.log_le_log (mul_pos (hp (A ∪ B ∪ C)) (hp B)) h
  simpa only [Real.log_mul (hp (A ∪ B ∪ C)).ne' (hp B).ne',
    Real.log_mul (hp (A ∪ B)).ne' (hp (B ∪ C)).ne'] using hl

end D5.S3.Resource.LogDet.KoteljanskiiPrincipalBlocks
