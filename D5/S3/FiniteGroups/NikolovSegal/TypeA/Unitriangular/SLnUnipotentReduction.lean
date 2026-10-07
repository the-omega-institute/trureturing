/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnipotentBlocks
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace NikolovSegal.SLnUnipotentWidth
open Matrix
universe u
variable {F : Type u} [Field F] {r : ℕ}

theorem mul_lowerRad_inl (g : BlockSL r F) (v : Fin r → F)
    (i : Fin r ⊕ Fin 1) (j : Fin r) :
    (g * lowerRad v).val i (Sum.inl j) =
      g.val i (Sum.inl j) + g.val i (Sum.inr 0) * v j := by
  simp [SpecialLinearGroup.coe_mul,lowerRad,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]

theorem mul_lowerRad_inr (g : BlockSL r F) (v : Fin r → F)
    (i : Fin r ⊕ Fin 1) :
    (g * lowerRad v).val i (Sum.inr 0) = g.val i (Sum.inr 0) := by
  simp [SpecialLinearGroup.coe_mul,lowerRad,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]

theorem mul_upperRad_inl (g : BlockSL r F) (v : Fin r → F)
    (i : Fin r ⊕ Fin 1) (j : Fin r) :
    (g * upperRad v).val i (Sum.inl j) = g.val i (Sum.inl j) := by
  simp [SpecialLinearGroup.coe_mul,upperRad,Matrix.mul_apply,Fintype.sum_sum_type,Matrix.one_apply]

theorem mul_upperRad_inr (g : BlockSL r F) (v : Fin r → F)
    (i : Fin r ⊕ Fin 1) :
    (g * upperRad v).val i (Sum.inr 0) =
      g.val i (Sum.inr 0) + (fun j => g.val i (Sum.inl j)) ⬝ᵥ v := by
  simp [SpecialLinearGroup.coe_mul,upperRad,Matrix.mul_apply,Fintype.sum_sum_type,
    dotProduct,add_comm]

/-- One actual lower-radical operation supplies a nonzero earlier entry in
the last row. The only input is the genuine nonzero row of an SL matrix. -/
theorem prepare_last_row (hr : 0 < r) (g : BlockSL r F) :
    ∃ v : Fin r → F, ∃ i : Fin r,
      (g * lowerRad v).val (Sum.inr 0) (Sum.inl i) ≠ 0 := by
  classical
  by_cases h : ∃ i : Fin r, g.val (Sum.inr 0) (Sum.inl i) ≠ 0
  · obtain ⟨i,hi⟩ := h
    exact ⟨0,i,by simpa using hi⟩
  · push Not at h
    have hn : ∃ j : Fin r ⊕ Fin 1, g.val (Sum.inr 0) j ≠ 0 := by
      by_contra hh
      push Not at hh
      apply g.row_ne_zero (Sum.inr 0)
      funext j
      exact hh j
    have hl : g.val (Sum.inr 0) (Sum.inr 0) ≠ 0 := by
      obtain ⟨j,hj⟩ := hn
      cases j with
      | inl j => exact False.elim (hj (h j))
      | inr j => simpa [show j = 0 from Subsingleton.elim _ _] using hj
    let i : Fin r := ⟨0,hr⟩
    refine ⟨Pi.single i 1,i,?_⟩
    rw [mul_lowerRad_inl,h i]
    simpa using hl

/-- Actual determinant-one rank reduction, with exactly four radical
positions. There is no pivot, flag, cardinality or decomposition premise. -/
theorem rank_reduction (hr : 0 < r) (g : BlockSL r F) :
    ∃ B : SpecialLinearGroup (Fin r) F, ∃ a b c d : Fin r → F,
      g = upperRad a * embed B * lowerRad b * upperRad c * lowerRad d := by
  classical
  obtain ⟨v₁,i,hi⟩ := prepare_last_row hr g
  let g₁ := g * lowerRad v₁
  let v₂ : Fin r → F := Pi.single i ((1-g₁.val (Sum.inr 0) (Sum.inr 0)) /
    g₁.val (Sum.inr 0) (Sum.inl i))
  let g₂ := g₁ * upperRad v₂
  have h₂ : g₂.val (Sum.inr 0) (Sum.inr 0) = 1 := by
    rw [mul_upperRad_inr]
    simp only [v₂,dotProduct_single]
    field_simp [show g₁.val (Sum.inr 0) (Sum.inl i) ≠ 0 from hi]
    ring
  let v₃ := fun j => -g₂.val (Sum.inr 0) (Sum.inl j)
  let g₃ := g₂ * lowerRad v₃
  have h₃l : ∀ j : Fin r, g₃.val (Sum.inr 0) (Sum.inl j) = 0 := by
    intro j
    rw [mul_lowerRad_inl,h₂]
    simp [v₃]
  have h₃r : g₃.val (Sum.inr 0) (Sum.inr 0) = 1 := by
    rw [mul_lowerRad_inr]
    exact h₂
  let B₀ := g₃.val.submatrix Sum.inl Sum.inl
  let a := fun j => g₃.val (Sum.inl j) (Sum.inr 0)
  have hform : g₃.val = fromBlocks B₀ (fun j _ => a j) 0 1 := by
    ext j k
    cases j with
    | inl j =>
      cases k with
      | inl k => rfl
      | inr k => simp [a,show k = 0 from Subsingleton.elim _ _]
    | inr j =>
      cases k with
      | inl k => simpa [show j = 0 from Subsingleton.elim _ _] using h₃l k
      | inr k => simpa [show j = 0 from Subsingleton.elim _ _,
          show k = 0 from Subsingleton.elim _ _] using h₃r
  have hdet : B₀.det = 1 := by
    have hd := g₃.property
    rw [hform,det_fromBlocks_zero₂₁] at hd
    simpa using hd
  let B : SpecialLinearGroup (Fin r) F := ⟨B₀,hdet⟩
  have hfact : g₃ = upperRad a * embed B := by
    apply Subtype.ext
    simpa [SpecialLinearGroup.coe_mul,upperRad,embed,fromBlocks_multiply,B] using hform
  refine ⟨B,a,-v₃,-v₂,-v₁,?_⟩
  have hback : g = g₃ * (lowerRad v₃)⁻¹ * (upperRad v₂)⁻¹ * (lowerRad v₁)⁻¹ := by
    dsimp [g₃,g₂,g₁]
    group
  simpa [hfact,upperRad_inv,lowerRad_inv,mul_assoc] using hback

end NikolovSegal.SLnUnipotentWidth
