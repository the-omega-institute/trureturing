/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/TotientPrimeProducts
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/TotientPrimeProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The reciprocal totient density is a product over the distinct prime divisors. -/

import Mathlib.Data.Nat.Totient
import Mathlib.Basic.Real.Basic

/-! The reciprocal totient density as a product over distinct prime divisors. -/

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.TotientPrimeProducts

open scoped BigOperators
open Finset

theorem totient_prime_product {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / Nat.totient n =
      ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have ht : (Nat.totient n : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    simpa only [one_div] using h
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [ht, div_mul_eq_div_mul_one_div, div_self hnR, one_mul, one_div,
    prod_inv_distrib]

end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.TotientPrimeProducts
