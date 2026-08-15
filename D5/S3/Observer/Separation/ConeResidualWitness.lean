/- GID: D5/S3/Observer/Separation/ConeResidualWitness
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/ConeResidualWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A closed convex cone residual gives its canonical separating dual witness. -/

import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/- Library-search audit trail (2026-08-16):
   * Repository searches for cone residuals, inner duals, and negative squared-norm
     separation found no matching declaration.
   * Pinned Mathlib provides `ProperCone.innerDual` and `ProperCone.mem_innerDual`
     for the dual cone.
   * Pinned Mathlib provides `exists_norm_eq_iInf_of_complete_convex` and
     `norm_eq_iInf_iff_real_inner_le_zero` for the metric projection and its
     variational inequality; both are imported and applied below.
   * Loogle confirmed those declarations and found no exact residual-witness wrapper.
     LeanSearch returned cone infrastructure but no exact decomposition theorem. -/

namespace D5.S3.Observer.Separation.ConeResidualWitness

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A chosen nearest point of `x` in the closed convex cone `C`. -/
noncomputable def coneProjection (C : ProperCone ℝ E) (x : E) : E :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex
      C.nonempty C.isClosed.isComplete C.convex x)

/-- The negative residual from the cone projection is the canonical dual witness.
Outside the cone it is nonnegative on the cone and evaluates on the separated point
as the strictly negative squared residual norm. -/
theorem cone_residual_observer_duality (C : ProperCone ℝ E) (x : E) :
    let p := coneProjection C x
    let r := x - p
    let w := -r
    w ∈ ProperCone.innerDual (C : Set E) ∧
      (x ∉ C →
        (∀ c ∈ C, 0 ≤ inner ℝ w c) ∧
          inner ℝ w x = -‖r‖ ^ 2 ∧
            inner ℝ w x < 0) := by
  let p := coneProjection C x
  let r := x - p
  let w := -r
  change w ∈ ProperCone.innerDual (C : Set E) ∧
    (x ∉ C →
      (∀ c ∈ C, 0 ≤ inner ℝ w c) ∧
        inner ℝ w x = -‖r‖ ^ 2 ∧
          inner ℝ w x < 0)
  have hprojection :=
    Classical.choose_spec
      (exists_norm_eq_iInf_of_complete_convex
        C.nonempty C.isClosed.isComplete C.convex x)
  have hp : p ∈ C := by
    simpa [p, coneProjection] using hprojection.1
  have hminimal : ‖x - p‖ = ⨅ c : (C : Set E), ‖x - c‖ := by
    simpa [p, coneProjection] using hprojection.2
  have hvariational : ∀ c ∈ C, inner ℝ r (c - p) ≤ 0 := by
    simpa [r] using
      (norm_eq_iInf_iff_real_inner_le_zero C.convex hp).mp hminimal
  have hinner_nonneg : 0 ≤ inner ℝ r p := by
    have hzero := hvariational 0 C.zero_mem
    rw [zero_sub, inner_neg_right] at hzero
    linarith
  have hinner_nonpos : inner ℝ r p ≤ 0 := by
    have htwop : (2 : ℝ) • p ∈ C := C.smul_mem hp (by norm_num)
    have htwo := hvariational ((2 : ℝ) • p) htwop
    simpa [two_smul] using htwo
  have horthogonal : inner ℝ r p = 0 :=
    le_antisymm hinner_nonpos hinner_nonneg
  have hpolar : ∀ c ∈ C, inner ℝ r c ≤ 0 := by
    intro c hc
    have hadd := hvariational (c + p) (C.add_mem hc hp)
    simpa using hadd
  have hdual : w ∈ ProperCone.innerDual (C : Set E) := by
    rw [ProperCone.mem_innerDual]
    intro c hc
    change 0 ≤ inner ℝ c (-r)
    rw [inner_neg_right, real_inner_comm]
    exact neg_nonneg.mpr (hpolar c hc)
  refine ⟨hdual, ?_⟩
  intro hx
  have hdecomp : x = p + r := by
    dsimp [r]
    abel
  have hrne : r ≠ 0 := by
    intro hrzero
    apply hx
    have hxp : x = p := sub_eq_zero.mp (by simpa [r] using hrzero)
    rw [hxp]
    exact hp
  have hidentity : inner ℝ w x = -‖r‖ ^ 2 := by
    simp [w, hdecomp, inner_add_right, horthogonal]
  refine ⟨?_, hidentity, ?_⟩
  · intro c hc
    rw [real_inner_comm]
    exact ProperCone.mem_innerDual.mp hdual hc
  · rw [hidentity]
    have hnorm : 0 < ‖r‖ := norm_pos_iff.mpr hrne
    nlinarith

#print axioms cone_residual_observer_duality

end D5.S3.Observer.Separation.ConeResidualWitness
