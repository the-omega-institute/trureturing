/- GID: D5/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero
   generality: I
   mirror-B: D5/B/S3/Zeros/PrimeRefinement/LocalNonzeroContinuationZero
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: At -2 prime Euler factors and finite windows are nonzero, but zeta vanishes. -/

import D5.S3.Weil.EulerProduct

/- Library-search audit trail (2026-08-25):
   * Repository hits: `EulerWindows.finite_euler_window_ne_zero` only covers positive real
     part, while `finite_prime_extraction_preserves_zeta_zero` requires a supplied strip zero.
     `ZeroData` has no inhabitant, so those declarations do not give this unconditional witness.
   * Mathlib hits: `riemannZeta_eulerProduct_hasProd` proves convergence for real part above one;
     `analyticOn_riemannZeta` gives the analytic completion off one; and
     `riemannZeta_neg_two_mul_nat_add_one` supplies the global trivial-zero bridge used below.
   * Searches for `EulerProduct`, `LSeries`, and `AnalyticOn` found those APIs. The exact name
     `AnalyticContinuation` had no repository or pinned-Mathlib hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.PrimeRefinement.LocalNonzeroContinuationZero

open D5.S3.Weil.EulerProduct

/-- Every prime-indexed local Euler factor is nonzero at the specified parameter. -/
def EveryPrimeEulerFactorNonzeroAt (s : ℂ) : Prop :=
  ∀ p : ℕ, p.Prime → (finiteEulerDenominator p s)⁻¹ ≠ 0

/-- At `-2`, excluding the non-prime base `1` already suffices for local nonvanishing.
Thus primality is not load-bearing for this finite algebraic fact. -/
theorem local_euler_factor_ne_zero_of_ne_one (p : ℕ) (hp : p ≠ 1) :
    (finiteEulerDenominator p (-2))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  simp only [finiteEulerDenominator, neg_neg, Complex.cpow_two]
  intro hzero
  apply hp
  have hpSq : p ^ 2 = 1 := by
    exact_mod_cast (sub_eq_zero.mp hzero).symm
  nlinarith

#print axioms local_euler_factor_ne_zero_of_ne_one

/-- The exclusion of base `1` is necessary when prime indexing is weakened to arbitrary bases. -/
theorem base_one_exclusion_is_necessary :
    (finiteEulerDenominator 1 (-2))⁻¹ = 0 := by
  simp [finiteEulerDenominator]

#print axioms base_one_exclusion_is_necessary

/-- Pointwise nonzero prime Euler factors, and all their finite windows, coexist with a zero of
the analytically continued zeta function. No infinite product at `-2` is asserted. -/
theorem local_euler_nonzero_continuation_zero_counterexample :
    ∃ s : ℂ,
      EveryPrimeEulerFactorNonzeroAt s ∧
      (∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → finiteEulerProduct S s ≠ 0) ∧
      riemannZeta s = 0 := by
  let s : ℂ := -2
  have hLocal : EveryPrimeEulerFactorNonzeroAt s := by
    intro p hp
    exact local_euler_factor_ne_zero_of_ne_one p hp.ne_one
  refine ⟨s, hLocal, ?_, ?_⟩
  · intro S hPrime
    rw [finiteEulerProduct, Finset.prod_ne_zero_iff]
    intro p hpS
    exact hLocal p (hPrime p hpS)
  · simpa [s] using riemannZeta_neg_two_mul_nat_add_one 0

#print axioms local_euler_nonzero_continuation_zero_counterexample

example : finiteEulerProduct ∅ (-2) = 1 := by
  simp [finiteEulerProduct]

example : finiteEulerProduct {2} (-2) ≠ 0 := by
  simpa [finiteEulerProduct] using
    local_euler_factor_ne_zero_of_ne_one 2 (by norm_num)

end D5.S3.Zeros.PrimeRefinement.LocalNonzeroContinuationZero
