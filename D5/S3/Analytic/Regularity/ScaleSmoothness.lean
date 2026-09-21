/- GID: D5/S3/Analytic/Regularity/ScaleSmoothness
   generality: G
   mirror-B: D5/B/S3/Analytic/Regularity/ScaleSmoothness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smoothness on a closed interval from derivatives across arbitrary normed-space grades. -/

/- Source: the supplied ExactScaleProof.lean, SHA256
   5fa23d889b7fba4dd29149d9b9b5aa2fe16284cda5878b4849d7555b4a718d24.
   The statement and proof are retained; a namespace and theorem name are added.
   Mathlib calculus is used under Apache-2.0, as described in LICENSE. -/

import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Set
open scoped ContDiff
set_option autoImplicit false

namespace D5.S3.Analytic.Regularity.ScaleSmoothness

/-- A family of paths is smooth on the same closed interval when each derivative
is a smooth function of a path at a fixed shifted grade. -/
theorem cont_diff_on_scale_of_has_deriv_within_at : ∀ (E : ℕ → Type) [∀ m, NormedAddCommGroup (E m)]
    [∀ m, NormedSpace ℝ (E m)]
    (r : ℕ) (T : ℝ), 0 < T →
    ∀ (u : ∀ m, ℝ → E m) (F : ∀ m, E (m + r) → E m),
    (∀ m, ContDiff ℝ ∞ (F m)) →
    (∀ m t, t ∈ Icc 0 T →
      HasDerivWithinAt (u m) (F m (u (m + r) t)) (Icc 0 T) t) →
    ∀ m, ContDiffOn ℝ ∞ (u m) (Icc 0 T) := by
  intro E instN instS r T hT u F hF hd
  have hfinite : ∀ n m : ℕ, ContDiffOn ℝ n (u m) (Icc 0 T) := by
    intro n
    induction n with
    | zero =>
      intro m
      exact contDiffOn_zero.mpr (HasDerivWithinAt.continuousOn (hd m))
    | succ n ih =>
      intro m
      rw [Nat.cast_add, Nat.cast_one,
        contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
      refine ⟨fun t ht => (hd m t ht).differentiableWithinAt, by simp, ?_⟩
      exact (((hF m).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp_contDiffOn
        (ih (m + r))).congr (fun t ht =>
          (hd m t ht).derivWithin ((uniqueDiffOn_Icc hT) t ht))
  intro m
  exact contDiffOn_infty.mpr (fun n => hfinite n m)

end D5.S3.Analytic.Regularity.ScaleSmoothness
