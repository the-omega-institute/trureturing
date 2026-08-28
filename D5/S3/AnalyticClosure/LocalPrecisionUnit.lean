/- GID: D5/S3/AnalyticClosure/LocalPrecisionUnit
   generality: I
   mirror-B: D5/B/S3/AnalyticClosure/LocalPrecisionUnit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The p-adic norm of the prime fixes its real logarithmic precision unit. -/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.AnalyticClosure.LocalPrecisionUnit

open scoped BigOperators

/- The source length is constructed from the canonical norm and logarithm. -/
noncomputable def precisionLength {p : ℕ} [Fact p.Prime] (x : ℚ_[p]) : ℝ :=
  -Real.log ‖x‖

theorem local_precision_unit (p : ℕ) [Fact p.Prime] :
    (Real.exp (-precisionLength (p : ℚ_[p])) = ‖(p : ℚ_[p])‖ ∧
      precisionLength (p : ℚ_[p]) = Real.log (p : ℝ) ∧
      (∀ ell : ℝ,
        Real.exp (-ell) = ‖(p : ℚ_[p])‖ →
          ell = precisionLength (p : ℚ_[p]))) ∧
    (∀ s : ℝ, (p : ℝ) ^ (-s) = Real.exp (-s * Real.log (p : ℝ))) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Nat.Prime.pos Fact.out)
  have hnorm : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
    exact Padic.norm_p
  have hlength : precisionLength (p : ℚ_[p]) = Real.log (p : ℝ) := by
    unfold precisionLength
    rw [hnorm]
    rw [Real.log_inv]
    ring
  constructor
  · constructor
    · rw [hlength, hnorm]
      rw [Real.exp_neg, Real.exp_log hp]
    · constructor
      · exact hlength
      · intro ell hell
        apply neg_injective
        apply Real.exp_injective
        calc
          Real.exp (-ell) = ‖(p : ℚ_[p])‖ := hell
          _ = Real.exp (-precisionLength (p : ℚ_[p])) := by
            rw [hlength, hnorm, Real.exp_neg, Real.exp_log hp]
  · intro s
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring

#print axioms local_precision_unit

end D5.S3.AnalyticClosure.LocalPrecisionUnit
