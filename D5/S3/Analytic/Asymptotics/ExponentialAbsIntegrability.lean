/- GID: D5/S3/Analytic/Asymptotics/ExponentialAbsIntegrability
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/ExponentialAbsIntegrability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-sided exponential is integrable at every positive rate. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: The Tau Ceti contributors
SPDX-License-Identifier: Apache-2.0

Adapted source port: the proof is extracted without mathematical changes from
D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy.lean,
whose source is TauCetiProject/TauCeti at
bbd2f34ff81c827b099c0c58d05372c6091ac050,
TauCeti/MeasureTheory/Integral/ExpDecay.lean. Both analytic consumers import
this common owner. Replace it with a direct Mathlib declaration when an
equivalent becomes available at this repository's pinned revision.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

open MeasureTheory Set

namespace D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability

/-- The two-sided real exponential is integrable at every positive rate. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-(a * |x|))) := by
  have hIic : IntegrableOn (fun x : ℝ => Real.exp (-(a * |x|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun (fun x hx => ?_)
      measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.mp hx)]
    ring_nf
  have hIoi : IntegrableOn (fun x : ℝ => Real.exp (-(a * |x|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hx)]
    ring_nf
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

end D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability
