/- GID: D5/S3/Arith/GoldenLocalThreshold
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenLocalThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boundary marginal bounds make a prime exponent locally optimal at a common price. -/

import D5.S3.Arith.GoldenResourceOptimalInteger

/- Library-search audit trail (2026-09-06):
   * Repository searches for local-objective maximality and arbitrary-price threshold theorems
     found no equal or stronger public result. `GoldenResourceOptimalInteger` has a private local
     optimum only at price 1/25 and at the exponents of 5040, so it cannot instantiate this theorem.
   * The frozen `golden_layer_strict_decrease` supplies exactly the pointwise marginal ordering;
     it does not supply the accumulated objective inequality proved below.
   * Pinned Mathlib supplies `monotoneOn_of_le_add_one`, `antitoneOn_of_add_one_le`, real logarithm
     identities, and ordered-ring arithmetic, but no theorem specialized to these prime layers. -/

namespace D5.S3.Arith.GoldenLocalThreshold

open D5.S3.Arith.GoldenResourceOptimalInteger

noncomputable section

/-- The contribution of one prime exponent to the logarithmic objective at price `lambda`. -/
def goldenPrimeLocalObjective (lambda : ℝ) (p a : ℕ) : ℝ :=
  Real.log ((1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹)) -
    lambda * a * Real.log p

private theorem golden_prime_local_objective_diff {p : ℕ} (hp : p.Prime)
    (lambda : ℝ) (a : ℕ) :
    goldenPrimeLocalObjective lambda p (a + 1) - goldenPrimeLocalObjective lambda p a =
      (goldenLayerMarginal p (a + 1) - lambda) * Real.log p := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpInvLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have ha : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  have hb : 0 < 1 - (p : ℝ)⁻¹ ^ (a + 1 + 1) :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  unfold goldenPrimeLocalObjective goldenLayerMarginal
  rw [Real.log_div hb.ne' (sub_pos.mpr hpInvLt).ne',
    Real.log_div ha.ne' (sub_pos.mpr hpInvLt).ne', Real.log_div hb.ne' ha.ne']
  push_cast
  field_simp [hpLog.ne']
  ring

/-- Boundary marginal inequalities make an exponent optimal in its prime direction. -/
theorem golden_prime_local_objective_maximal_of_threshold {p a : ℕ} (hp : p.Prime)
    (lambda : ℝ) (hupper : goldenLayerMarginal p (a + 1) ≤ lambda)
    (hlower : a = 0 ∨ lambda ≤ goldenLayerMarginal p a) :
    ∀ b, goldenPrimeLocalObjective lambda p b ≤ goldenPrimeLocalObjective lambda p a := by
  have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have up : MonotoneOn (goldenPrimeLocalObjective lambda p) (Set.Iic a) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Iic
    intro k _ _ hnext
    have hgain : lambda ≤ goldenLayerMarginal p (k + 1) := by
      rcases hlower with rfl | hlower
      · simp at hnext
      · rcases eq_or_lt_of_le (show k + 1 ≤ a from hnext) with heq | hlt
        · simpa [heq] using hlower
        · exact hlower.trans (golden_layer_strict_decrease hp (by omega) hlt).le
    have hstep := mul_nonneg (sub_nonneg.mpr hgain) hpLog.le
    rw [← golden_prime_local_objective_diff hp lambda k] at hstep
    exact sub_nonneg.mp hstep
  have down : AntitoneOn (goldenPrimeLocalObjective lambda p) (Set.Ici a) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Ici
    intro k _ hk _
    have hgain : goldenLayerMarginal p (k + 1) ≤ lambda := by
      rcases eq_or_lt_of_le (Nat.succ_le_succ hk) with heq | hlt
      · have hak : a = k := Nat.succ.inj heq
        subst k
        exact hupper
      · exact (golden_layer_strict_decrease hp (by omega) hlt).le.trans hupper
    have hstep := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hgain) hpLog.le
    rw [← golden_prime_local_objective_diff hp lambda k] at hstep
    exact sub_nonpos.mp hstep
  intro b
  rcases le_total b a with hba | hab
  · exact up hba (by simp) hba
  · exact down (by simp) hab hab

end

end D5.S3.Arith.GoldenLocalThreshold
