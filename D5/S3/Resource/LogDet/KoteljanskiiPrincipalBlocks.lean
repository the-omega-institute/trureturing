/- GID: D5/S3/Resource/LogDet/KoteljanskiiPrincipalBlocks
   generality: G
   mirror-B: D5/B/S3/Resource/LogDet/KoteljanskiiPrincipalBlocks
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Koteljanskii determinant and logarithm inequalities for Hermitian principal blocks. -/

import D5.S3.Resource.LogDet.LogDetInformationSubmodularity

/-! Determinant submodularity of Hermitian positive definite principal blocks. -/

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Resource.LogDet.KoteljanskiiPrincipalBlocks

private theorem det_mono {α : Type*} [Fintype α] [DecidableEq α]
    {P Q : Matrix α α ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (hPQ : (Q - P).PosSemidef) : P.det.re ≤ Q.det.re := by
  classical
  cases isEmpty_or_nonempty α with
  | inl h => exact le_of_eq (congrArg (fun M : Matrix α α ℂ => M.det.re)
      (Subsingleton.elim P Q))
  | inr h =>
    exact (Real.log_le_log_iff hP.det_pos.1 hQ.det_pos.1).mp
      (LogDetInformationSubmodularity.log_det_mono hP hQ hPQ)

private theorem schur_factor {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hH : H.PosDef) :
    let P := H.submatrix Sum.inl Sum.inl
    let X := H.submatrix Sum.inl Sum.inr
    let Q := H.submatrix Sum.inr Sum.inr
    (Q - Xᴴ * P⁻¹ * X).PosDef ∧
      H.det.re = P.det.re * (Q - Xᴴ * P⁻¹ * X).det.re := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  have hP : P.PosDef := hH.submatrix Sum.inl_injective
  have h21 : H.submatrix Sum.inr Sum.inl = Xᴴ := by
    dsimp only [X]
    rw [conjTranspose_submatrix, hH.isHermitian.eq]
  have hb : fromBlocks P X Xᴴ Q = H := by
    rw [← h21]
    exact fromBlocks_toBlocks H
  let := hP.isUnit.invertible
  have hs : (Q - Xᴴ * P⁻¹ * X).PosSemidef :=
    (hP.fromBlocks₁₁ X Q).mp (hb.symm ▸ hH.posSemidef)
  have hd : H.det = P.det * (Q - Xᴴ * P⁻¹ * X).det := by
    rw [← hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hspos : (Q - Xᴴ * P⁻¹ * X).PosDef := by
    apply hs.posDef_iff_det_ne_zero.mpr
    intro hz
    rw [hz, mul_zero] at hd
    exact (ne_of_gt hH.det_pos) hd
  refine ⟨hspos, ?_⟩
  change H.det.re = P.det.re * (Q - Xᴴ * P⁻¹ * X).det.re
  simp only [hd, Complex.mul_re, hP.det_pos.2.symm, hspos.det_pos.2.symm,
    Complex.zero_im, mul_zero, sub_zero]

private theorem fischer {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (H : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hH : H.PosDef) :
    H.det.re ≤ (H.submatrix Sum.inl Sum.inl).det.re *
      (H.submatrix Sum.inr Sum.inr).det.re := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  have hP : P.PosDef := hH.submatrix Sum.inl_injective
  have hQ : Q.PosDef := hH.submatrix Sum.inr_injective
  obtain ⟨hs, hd⟩ := schur_factor H hH
  have hc : (Xᴴ * P⁻¹ * X).PosSemidef :=
    hP.posSemidef.inv.conjTranspose_mul_mul_same X
  have ho : (Q - (Q - Xᴴ * P⁻¹ * X)).PosSemidef := by
    convert hc using 1
    abel
  have hm := det_mono hs hQ ho
  rw [hd]
  exact mul_le_mul_of_nonneg_left hm hP.det_pos.1.le

private theorem schur_submatrix {α β γ : Type*} [Fintype α] [DecidableEq α]
    (P : Matrix α α ℂ) (X : Matrix α β ℂ) (Q : Matrix β β ℂ) (e : γ → β) :
    (Q - Xᴴ * P⁻¹ * X).submatrix e e =
      Q.submatrix e e - (X.submatrix id e)ᴴ * P⁻¹ * X.submatrix id e := by
  change Q.submatrix e e - (Xᴴ * P⁻¹ * X).submatrix e e = _
  rw [submatrix_mul _ _ e id e Function.bijective_id,
    submatrix_mul _ _ e id id Function.bijective_id, submatrix_id_id,
    conjTranspose_submatrix]

private theorem block_koteljanskii {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (H : Matrix (β ⊕ (α ⊕ γ)) (β ⊕ (α ⊕ γ)) ℂ) (hH : H.PosDef) :
    H.det.re * (H.submatrix Sum.inl Sum.inl).det.re ≤
      (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det.re *
        (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det.re := by
  let P := H.submatrix Sum.inl Sum.inl
  let X := H.submatrix Sum.inl Sum.inr
  let Q := H.submatrix Sum.inr Sum.inr
  let S := Q - Xᴴ * P⁻¹ * X
  have hP : P.PosDef := hH.submatrix Sum.inl_injective
  obtain ⟨hs, hd⟩ := schur_factor H hH
  have hA := hH.submatrix
    (Function.injective_id.sumMap (@Sum.inl_injective α γ))
  have hC := hH.submatrix
    (Function.injective_id.sumMap (@Sum.inr_injective α γ))
  have hdA := (schur_factor _ hA).2
  have hdC := (schur_factor _ hC).2
  change (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det.re =
    P.det.re * (Q.submatrix Sum.inl Sum.inl -
      (X.submatrix id Sum.inl)ᴴ * P⁻¹ * X.submatrix id Sum.inl).det.re at hdA
  change (H.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det.re =
    P.det.re * (Q.submatrix Sum.inr Sum.inr -
      (X.submatrix id Sum.inr)ᴴ * P⁻¹ * X.submatrix id Sum.inr).det.re at hdC
  rw [← schur_submatrix P X Q Sum.inl] at hdA
  rw [← schur_submatrix P X Q Sum.inr] at hdC
  have hf := fischer S hs
  rw [hdA, hdC, hd]
  nlinarith [mul_le_mul_of_nonneg_left hf (sq_nonneg P.det.re)]

private theorem principal_product {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  let eAC := Equiv.Finset.union A C hAC
  have hBU : Disjoint B (A ∪ C) :=
    Finset.disjoint_union_right.mpr ⟨hAB.symm, hBC⟩
  let e := (Equiv.sumCongr (Equiv.refl ↥B) eAC).trans
    (Equiv.Finset.union B (A ∪ C) hBU)
  let f : ↥B ⊕ (↥A ⊕ ↥C) → ι := fun x => (e x).val
  let M := H.submatrix f f
  have hM : M.PosDef := hH.submatrix (Subtype.val_injective.comp e.injective)
  have hm := block_koteljanskii M hM
  have hd : M.det =
      (H.submatrix (Subtype.val : ↥(B ∪ (A ∪ C)) → ι) Subtype.val).det :=
    det_submatrix_equiv_self e
      (H.submatrix (Subtype.val : ↥(B ∪ (A ∪ C)) → ι) Subtype.val)
  have hB : M.submatrix Sum.inl Sum.inl =
      H.submatrix (Subtype.val : ↥B → ι) Subtype.val := rfl
  have hBA :
      (M.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)).det =
        (H.submatrix (Subtype.val : ↥(B ∪ A) → ι) Subtype.val).det := by
    calc
      _ = ((H.submatrix (Subtype.val : ↥(B ∪ A) → ι) Subtype.val).submatrix
          (Equiv.Finset.union B A hAB.symm) (Equiv.Finset.union B A hAB.symm)).det := by
        congr 1
        ext i j
        cases i <;> cases j <;> rfl
      _ = _ := det_submatrix_equiv_self _ _
  have hBC' :
      (M.submatrix (Sum.map id Sum.inr) (Sum.map id Sum.inr)).det =
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det := by
    calc
      _ = ((H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).submatrix
          (Equiv.Finset.union B C hBC) (Equiv.Finset.union B C hBC)).det := by
        congr 1
        ext i j
        cases i <;> cases j <;> rfl
      _ = _ := det_submatrix_equiv_self _ _
  rw [hd, hB, hBA, hBC'] at hm
  have hU : B ∪ (A ∪ C) = A ∪ B ∪ C :=
    (Finset.union_left_comm B A C).trans (Finset.union_assoc A B C).symm
  rw [hU, Finset.union_comm B A] at hm
  exact hm

/-- Koteljanskii's inequality, with determinants read as positive real numbers. -/
theorem koteljanskii {ι : Type*} [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.PosDef) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (H.submatrix (Subtype.val : ↥(A ∪ B ∪ C) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥B → ι) Subtype.val).det.re ≤
      (H.submatrix (Subtype.val : ↥(A ∪ B) → ι) Subtype.val).det.re *
        (H.submatrix (Subtype.val : ↥(B ∪ C) → ι) Subtype.val).det.re := by
  exact principal_product H hH A B C hAB hAC hBC

/-- The logarithmic principal-block inequality, including empty blocks. -/
theorem result {ι : Type*} [DecidableEq ι]
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
