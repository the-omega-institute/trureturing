/- GID: D5/S3/Geometry/Hyperideal/LengthGramRadialImage
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramRadialImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.StdSimplex]
   utility: none
   digest: The normalized radial image is exactly the nonnegative coefficient slice cut out by the Gram halfspaces. -/

import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Geometry.Hyperideal.LengthGramRadialImage

abbrev V := Fin 4 → ℝ

def halfspaceSlice (l : Fin 6 → ℝ) : Set V :=
  {x | gramQuadratic l x = -1 ∧
    (∀ i, 0 ≤ x i) ∧
    (∀ i, ∑ j, lengthGram l i j * x j ≤ 0)}

private lemma gramQuadratic_div (l : Fin 6 → ℝ) (x : V) (c : ℝ) (hc : c ≠ 0) :
    gramQuadratic l (fun i => x i / c) = gramQuadratic l x / c ^ 2 := by
  unfold gramQuadratic
  have hrow (i : Fin 4) :
      (∑ j, lengthGram l i j * (x j / c)) =
        (∑ j, lengthGram l i j * x j) / c := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [hrow]
  ring

private lemma radial_row_div (l : Fin 6 → ℝ) (i : Fin 4) (x : V) (c : ℝ) :
    (∑ j, lengthGram l i j * (x j / c)) =
      (∑ j, lengthGram l i j * x j) / c := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! The coefficient-space form of the original eight-support image statement. -/
theorem radial_image_halfspace_slice (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k) :
    radial l '' cutBody l = halfspaceSlice l := by
  classical
  obtain ⟨_, _, _, hnegative, _, _, _, _, hnormalized, _⟩ :=
    shared_radial_body l hl
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hsqrt : 0 < Real.sqrt (-gramQuadratic l v) :=
      Real.sqrt_pos.mpr (neg_pos.mpr (hnegative v hv))
    refine ⟨hnormalized v hv, ?_, ?_⟩
    · intro i
      exact div_nonneg (hv.1.1 i) hsqrt.le
    · intro i
      change (∑ j, lengthGram l i j *
        (v j / Real.sqrt (-gramQuadratic l v))) ≤ 0
      rw [radial_row_div]
      exact div_nonpos_of_nonpos_of_nonneg (hv.2 i) hsqrt.le
  · intro hx
    rcases hx with ⟨hxq, hxnonneg, hxsupport⟩
    have hxne : x ≠ 0 := by
      intro hzero
      subst x
      simp [gramQuadratic] at hxq
    have hsumpos : 0 < ∑ i, x i := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hxne (funext h)
      apply (Finset.sum_pos_iff_of_nonneg (fun i _ => hxnonneg i)).mpr
      exact ⟨i, Finset.mem_univ _, lt_of_le_of_ne (hxnonneg i) (Ne.symm hi)⟩
    let s : ℝ := ∑ i, x i
    let v : V := fun i => x i / s
    have hs : 0 < s := hsumpos
    have hvsum : ∑ i, v i = 1 := by
      dsimp [v, s]
      rw [← Finset.sum_div]
      field_simp
    have hvnonneg : ∀ i, 0 ≤ v i := by
      intro i
      exact div_nonneg (hxnonneg i) hs.le
    have hvsupport : ∀ i, ∑ j, lengthGram l i j * v j ≤ 0 := by
      intro i
      dsimp [v]
      rw [radial_row_div]
      exact div_nonpos_of_nonpos_of_nonneg (hxsupport i) hs.le
    have hv : v ∈ cutBody l := by
      exact ⟨⟨hvnonneg, hvsum⟩, hvsupport⟩
    have hqv : gramQuadratic l v = -1 / s ^ 2 := by
      rw [gramQuadratic_div l x s hs.ne', hxq]
    have hsqrt : Real.sqrt (-gramQuadratic l v) = 1 / s := by
      rw [hqv]
      have hsq : -( -1 / s ^ 2) = (1 / s) ^ 2 := by
        field_simp
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hs)]
    refine ⟨v, hv, ?_⟩
    funext i
    simp only [radial, v, hsqrt]
    field_simp

end D5.S3.Geometry.Hyperideal.LengthGramRadialImage

