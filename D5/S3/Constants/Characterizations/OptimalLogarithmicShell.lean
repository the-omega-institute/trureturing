/- GID: D5/S3/Constants/Characterizations/OptimalLogarithmicShell
   generality: G
   mirror-B: D5/B/S3/Constants/Characterizations/OptimalLogarithmicShell
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The exponential unit uniquely minimizes cost per logarithmic scale above one. -/

/- Library-search audit trail (2026-08-28):
   * D5 searches found the independent exponential-flow characterization, but no minimum theorem
     for the logarithmic shell cost.
   * Pinned Mathlib's `Real.exp_one_mul_le_exp` gives the global lower bound after the logarithmic
     substitution. `Real.log_lt_sub_one_of_pos` makes equality strict away from the minimizer.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Characterizations.OptimalLogarithmicShell

open Set

/-- On the domain above one, cost per logarithmic scale has its unique global minimum at the
exponential unit. -/
theorem exp_one_unique_logarithmic_shell_minimizer :
    IsMinOn (fun beta : ℝ => beta / Real.log beta) (Ioi 1) (Real.exp 1) ∧
      ∀ beta ∈ Ioi (1 : ℝ),
        beta / Real.log beta = Real.exp 1 / Real.log (Real.exp 1) ->
          beta = Real.exp 1 := by
  constructor
  · rw [isMinOn_iff]
    intro beta hbeta
    have beta_pos : 0 < beta := lt_trans zero_lt_one hbeta
    have log_beta_pos : 0 < Real.log beta := Real.log_pos hbeta
    rw [Real.log_exp, div_one, le_div_iff₀ log_beta_pos]
    simpa only [Real.exp_log beta_pos] using
      (Real.exp_one_mul_le_exp (x := Real.log beta))
  · intro beta hbeta value_eq
    have beta_pos : 0 < beta := lt_trans zero_lt_one hbeta
    have log_beta_pos : 0 < Real.log beta := Real.log_pos hbeta
    have exp_one_pos : 0 < Real.exp 1 := Real.exp_pos 1
    have quotient_eq : beta / Real.log beta = Real.exp 1 := by
      simpa only [Real.log_exp, div_one] using value_eq
    have linear_eq : beta = Real.exp 1 * Real.log beta :=
      (div_eq_iff log_beta_pos.ne').mp quotient_eq
    have ratio_eq_log : beta / Real.exp 1 = Real.log beta := by
      apply (div_eq_iff exp_one_pos.ne').2
      simpa only [mul_comm] using linear_eq
    have log_ratio_eq :
        Real.log (beta / Real.exp 1) = beta / Real.exp 1 - 1 := by
      calc
        Real.log (beta / Real.exp 1) =
            Real.log beta - Real.log (Real.exp 1) :=
          Real.log_div beta_pos.ne' exp_one_pos.ne'
        _ = Real.log beta - 1 := by rw [Real.log_exp]
        _ = beta / Real.exp 1 - 1 := by rw [ratio_eq_log]
    have ratio_pos : 0 < beta / Real.exp 1 := div_pos beta_pos exp_one_pos
    have ratio_eq_one : beta / Real.exp 1 = 1 := by
      by_contra ratio_ne_one
      have strict_bound := Real.log_lt_sub_one_of_pos ratio_pos ratio_ne_one
      linarith
    exact (div_eq_one_iff_eq exp_one_pos.ne').mp ratio_eq_one

#print axioms exp_one_unique_logarithmic_shell_minimizer

end D5.S3.Constants.Characterizations.OptimalLogarithmicShell
