/- GID: D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct
   generality: G
   mirror-B: D5/B/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complex divisor sums factor into finite geometric products for every exponent. -/

import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false
noncomputable section

namespace D5.S3.Arith.DivisorGibbs.FiniteDivisorEulerProduct

open scoped BigOperators

/-- The Dirichlet polynomial over the actual positive divisors of `n`. -/
def Z (n : ℕ) (s : ℂ) : ℂ := ∑ d ∈ n.divisors, (d : ℂ) ^ (-s)

private def weight (s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (n : ℂ) ^ (-s), by simp⟩

private theorem weight_multiplicative (s : ℂ) : (weight s).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  refine ⟨by simp [weight], ?_⟩
  intro m n hm hn _
  simpa [weight, hm, hn, Nat.mul_ne_zero hm hn, Nat.cast_mul] using
    Complex.natCast_mul_natCast_cpow m n (-s)

private theorem zeta_weight (n : ℕ) (s : ℂ) :
    (ArithmeticFunction.zeta * weight s) n = Z n s := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  exact Finset.sum_congr rfl fun d hd => if_neg (Nat.pos_of_mem_divisors hd).ne'

/-- The finite Euler product holds for arbitrary complex `s`, including zero. -/
theorem divisor_sum_eq_euler_product (n : ℕ) (s : ℂ) (hn : 0 < n) :
    Z n s = ∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℂ) ^ (-s)) ^ j := by
  rw [← zeta_weight]
  rw [(ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (weight_multiplicative s)).multiplicative_factorization _ hn.ne']
  change (∏ p ∈ n.factorization.support,
    (ArithmeticFunction.zeta * weight s) (p ^ n.factorization p)) = _
  rw [Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  rw [zeta_weight, Z, Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- Extending the finite divisor sum by zero gives its natural-indexed infinite sum. -/
theorem divisor_sum_eq_tsum (n : ℕ) (s : ℂ) :
    Z n s = ∑' d : ℕ, if d ∈ n.divisors then (d : ℂ) ^ (-s) else 0 := by
  rw [tsum_eq_sum (s := n.divisors) (fun d hd => if_neg hd)]
  exact Finset.sum_congr rfl fun d hd => (if_pos hd).symm

example : 0 < (1 : ℕ) := Nat.zero_lt_one
example : ℂ := 0
example (n : ℕ) (hn : 0 < n) :
    Z n 0 = ∏ p ∈ n.primeFactors,
      ∑ j ∈ Finset.range (n.factorization p + 1), ((p : ℂ) ^ (-(0 : ℂ))) ^ j :=
  divisor_sum_eq_euler_product n 0 hn

#print axioms divisor_sum_eq_euler_product
#print axioms divisor_sum_eq_tsum

end D5.S3.Arith.DivisorGibbs.FiniteDivisorEulerProduct
