/- GID: D5/S0/Tower/Tribonacci/BinetRatio
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tribonacci Binet asymptotics give ratio convergence and eventual nearest integers. -/

import Mathlib
import D5.S0.Tower.Tribonacci.Binet

/- Provenance: Native proof over pinned mathlib. -/

/- SEARCH RECEIPT (2026-08-16, pinned repository and pinned mathlib):
   * `D5/S0/Tower/Tribonacci/Binet.lean:24-25` defines the Binet coefficient,
     and lines 87-91 provide the absolute-error limit reused below.
   * `D5/S0/Tower/Tribonacci/Values.lean:46-57` provides `1 < t`, positivity,
     and nonvanishing of the Tribonacci Perron root.
   * `D5/S0/Tower/Tribonacci/PerronRoot.lean:165-168` is the adjacent-term
     ratio limit; a search of the Tribonacci bucket found no main-term ratio limit.
   * `Mathlib/Analysis/SpecificLimits/Basic.lean:181-186` provides divergence
     of powers with base greater than one.
   * `Mathlib/Topology/Algebra/Order/Field.lean:212-215` provides
     `Filter.Tendsto.div_atTop` for a convergent numerator and divergent denominator.
   * `Mathlib/Algebra/Order/Round.lean:180-181` characterizes `round` by its
     half-open unit interval, supporting the direct nearest-integer corollary. -/

namespace D5.S0.Tower.Tribonacci.BinetRatio

open D5.S0.Tower.Tribonacci.Names
open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.Binet
open Filter

local notation "t" => tribonacciConstant

/-- The Tribonacci numbers divided by the Perron power converge to the Binet coefficient. -/
theorem tribonacci_div_pow_tendsto_binetCoefficient :
    Filter.Tendsto (fun n : Nat => (tribonacci n : Real) / t ^ n)
      Filter.atTop (nhds tribonacciBinetCoefficient) := by
  have hpow : Tendsto (fun n : Nat => t ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_tribonacciConstant
  have hquotient :
      Tendsto
        (fun n : Nat =>
          ((tribonacci n : Real) - tribonacciBinetCoefficient * t ^ n) / t ^ n)
        atTop (nhds 0) :=
    tribonacci_binet_tendsto_zero.div_atTop hpow
  have hidentity (n : Nat) :
      (tribonacci n : Real) / t ^ n =
        ((tribonacci n : Real) - tribonacciBinetCoefficient * t ^ n) / t ^ n +
          tribonacciBinetCoefficient := by
    field_simp [pow_ne_zero n tribonacciConstant_ne_zero]
    ring
  simpa only [hidentity, zero_add] using
    hquotient.add_const tribonacciBinetCoefficient

/-- Eventually the absolute Binet error is strictly below one half. -/
theorem tribonacci_eventually_abs_binet_error_lt_half :
    ∀ᶠ n : Nat in Filter.atTop,
      |(tribonacci n : Real) - tribonacciBinetCoefficient * t ^ n| < 1 / 2 := by
  have hball := tribonacci_binet_tendsto_zero.eventually
    (Metric.ball_mem_nhds (0 : Real) (by norm_num : (0 : Real) < 1 / 2))
  filter_upwards [hball] with n hn
  simpa [Real.dist_eq] using hn

/-- Eventually each Tribonacci number is the nearest integer to its Perron main term. -/
theorem tribonacci_eventually_eq_round_binet :
    ∀ᶠ n : Nat in Filter.atTop,
      Int.ofNat (tribonacci n) = round (tribonacciBinetCoefficient * t ^ n) := by
  filter_upwards [tribonacci_eventually_abs_binet_error_lt_half] with n hn
  rw [eq_comm, round_eq_iff]
  rw [abs_lt] at hn
  constructor <;> norm_num at hn ⊢ <;> linarith

#print axioms tribonacci_div_pow_tendsto_binetCoefficient
#print axioms tribonacci_eventually_abs_binet_error_lt_half
#print axioms tribonacci_eventually_eq_round_binet

end D5.S0.Tower.Tribonacci.BinetRatio
