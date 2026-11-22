/- GID: D5/S3/HilbertOperators/VisibleTwoStepDefect
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/VisibleTwoStepDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A two-step compression defect measures squared leakage out of a visible subspace. -/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HilbertOperators.VisibleTwoStepDefect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (V : Submodule ℝ E) [V.HasOrthogonalProjection] (T : E →L[ℝ] E)

/-- On a visible vector, compare two full steps with two successive projected steps. -/
noncomputable def defectForm (v : V) : ℝ :=
  inner ℝ (v : E) (V.starProjection (T (T v)) -
    V.starProjection (T (V.starProjection (T v))))

/-- For a symmetric time step the two-step defect is the squared norm of the
discarded component. Its vanishing for every visible vector characterizes invariance. -/
theorem visible_two_step_defect (hT : T.toLinearMap.IsSymmetric) :
    (∀ v : V, defectForm V T v = ‖T v - V.starProjection (T v)‖ ^ 2) ∧
    ((∀ v : V, defectForm V T v = 0) ↔ ∀ v : V, T v ∈ V) := by
  have formula (v : V) : defectForm V T v = ‖T v - V.starProjection (T v)‖ ^ 2 := by
    let r := T v - V.starProjection (T v)
    have drop (y : E) : inner ℝ (v : E) (V.starProjection y) = inner ℝ (v : E) y := by
      rw [← V.inner_starProjection_left_eq_right, V.starProjection_mem_subspace_eq_self]
    have orth : inner ℝ (V.starProjection (T v)) r = 0 :=
      (real_inner_comm _ _).trans
        (Submodule.starProjection_inner_eq_zero (K := V) (T v) _ (V.starProjection_apply_mem _))
    calc
      defectForm V T v = inner ℝ (v : E) (T r) := by
        simp only [defectForm, r, map_sub, inner_sub_right, drop]
      _ = inner ℝ (T v) r := (hT (v : E) r).symm
      _ = inner ℝ r r := by rw [show inner ℝ r r = inner ℝ (T v) r -
        inner ℝ (V.starProjection (T v)) r from inner_sub_left .., orth, sub_zero]
      _ = ‖r‖ ^ 2 := real_inner_self_eq_norm_sq r
  refine ⟨formula, ?_⟩
  constructor
  · intro vanishes v
    have zero : T v - V.starProjection (T v) = 0 := by
      simpa only [formula, sq_eq_zero_iff, norm_eq_zero] using vanishes v
    exact (sub_eq_zero.mp zero).symm ▸ V.starProjection_apply_mem (T v)
  · intro invariant v
    rw [formula, Submodule.starProjection_eq_self_iff.mpr (invariant v), sub_self, norm_zero]
    norm_num

#print axioms visible_two_step_defect

end D5.S3.HilbertOperators.VisibleTwoStepDefect
