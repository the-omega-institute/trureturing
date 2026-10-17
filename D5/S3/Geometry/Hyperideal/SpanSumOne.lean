/- GID: D5/S3/Geometry/Hyperideal/SpanSumOne
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/SpanSumOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.FiniteDimensional.Lemmas]
   utility: none
   digest: Four affine-independent points in a common sum-one hyperplane span that hyperplane. -/

import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Set
open Module
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.SpanSumOne

abbrev V := Fin 4 → ℝ

def sumOne : AffineSubspace ℝ V where
  carrier := {x | ∑ i, x i = 1}
  smul_vsub_vadd_mem' c p q r hp hq hr := by
    change (∑ i : Fin 4, (c * (p i - q i) + r i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp, hq, hr]
    ring

/-- A four-point affine-independent family in the sum-one hyperplane spans it. -/
theorem span_sumOne (v : Fin 4 → V) (hv : ∀ j, v j ∈ sumOne)
    (hi : AffineIndependent ℝ v) : affineSpan ℝ (range v) = sumOne := by
  classical
  have hlin : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro w hw
    have hsum : ∑ j, w j = 0 := by
      have he := congrArg (fun x : V => ∑ i, x i) hw
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
      rw [Finset.sum_comm] at he
      simp only [← Finset.mul_sum, show ∀ j, ∑ i, v j i = 1 from hv, mul_one] at he
      simpa using he
    exact fun j => hi.eq_zero_of_sum_eq_zero hsum hw j (Finset.mem_univ j)
  let B : Basis (Fin 4) ℝ V := basisOfPiSpaceOfLinearIndependent hlin
  have hB (i : Fin 4) : B i = v i := by simp [B]
  apply le_antisymm
  · exact affineSpan_le.mpr (by rintro x ⟨j, rfl⟩; exact hv j)
  · intro x hx
    let w : Fin 4 → ℝ := fun j => B.repr x j
    have he : ∑ j, w j • v j = x := by
      simpa only [hB, w] using B.sum_repr x
    have hw : ∑ j, w j = 1 := by
      have hh := congrArg (fun y : V => ∑ i, y i) he
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hh
      rw [Finset.sum_comm] at hh
      simp only [← Finset.mul_sum, show ∀ j, ∑ i, v j i = 1 from hv, mul_one] at hh
      exact hh.trans hx
    have hm := affineCombination_mem_affineSpan hw v
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw, he] at hm
    exact hm

#print axioms span_sumOne

end D5.S3.Geometry.Hyperideal.SpanSumOne
