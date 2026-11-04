/- GID: D5/S3/Quantum/Information/StrongSubadditivity/Physlib/ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog
   generality: G
   mirror-B: none(waiver:upstream-proof-closure)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed Physlib strong-subadditivity proof closure. -/

/- Adapted from leanprover-community/physlib, revision
2725b6f621901d4cd330869e9b77105045c1582e, QuantumInfo/ClassicalInfo/ForMathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean.
Changes: D5 import paths, bounded modules, and local supplier elaboration options.
Retire this port when the receiving pinned Mathlib provides the equivalent declarations.
Apache-2.0 license text is included in the sibling ForMathlib/Misc.lean. -/
/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

set_option relaxedAutoImplicit true

noncomputable section
open NNReal

namespace Real

lemma negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (exp (-1))) := by
  apply strictMonoOn_of_deriv_pos
  · exact convex_Icc 0 (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    linarith only [log_exp (-1), log_lt_log hx.left hx.right, deriv_negMulLog hx.left.ne']

lemma negMulLog_strictAntiOn : StrictAntiOn Real.negMulLog (Set.Ici (exp (-1))) := by
  apply strictAntiOn_of_deriv_neg
  · exact convex_Ici (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Ici' Set.nonempty_Iio, Set.mem_Ioi] at hx
    have hx' : x ≠ 0 := by grind [exp_nonneg]
    linarith [log_exp (-1), log_lt_log (exp_pos (-1)) hx, deriv_negMulLog hx']

lemma negMulLog_le_rexp_neg_one {x : ℝ} (hx : 0 ≤ x) : negMulLog x ≤ exp (-1) := by
  by_cases hp : x < exp (-1)
  · grw [negMulLog_strictMonoOn.monotoneOn (by grind) (by grind) hp.le]
    simp [negMulLog]
  by_cases hp' : Real.exp (-1) < x
  · grw [negMulLog_strictAntiOn.antitoneOn (by grind) (by grind) hp'.le]
    simp [negMulLog]
  · simp [show x = exp (-1) by order, negMulLog]

end Real
