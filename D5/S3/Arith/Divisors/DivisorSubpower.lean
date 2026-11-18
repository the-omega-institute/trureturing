/- GID: D5/S3/Arith/Divisors/DivisorSubpower
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/DivisorSubpower
   mirror-E: none(waiver:symbolic-uniform-divisor-bound)
   anchors: []
   utility: none
   digest: The number of positive divisors is bounded by every positive real power. -/

/- admission_basis: escape-witness. The uniform prime-factor product estimate is
   consumed by the Pascadi modular-zero partner count; this is the classical
   divisor subpower bound, with no novelty claim. -/

import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! # The classical divisor subpower bound

For every positive real exponent, the number of positive divisors of a nonzero
natural number is bounded by a constant times that power of the number.
The constant absorbs only finitely many small primes.
-/

namespace D5.S3.Arith.Divisors.DivisorSubpower

open Finset

/-- The classical uniform estimate `τ(n) ≪_ε n^ε`, for every `ε > 0`. -/
theorem card_divisors_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  classical
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let C : ℝ := 1 + (r - 1)⁻¹
  have hC : 1 ≤ C := by
    have := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [C]
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  have hsmall (p e : ℕ) (hp : 2 ≤ p) :
      (e : ℝ) + 1 ≤ C * ((p : ℝ) ^ ε) ^ e := by
    have he := e.cast_le_pow_div_sub hr
    have hone : (1 : ℝ) ≤ r ^ e := one_le_pow₀ hr.le
    have hbase : r ≤ (p : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hε.le
    have hpow := pow_le_pow_left₀ (zero_le_one.trans hr.le) hbase e
    have hbound : (e : ℝ) + 1 ≤ C * r ^ e := by
      dsimp [C]
      rw [div_eq_mul_inv] at he
      nlinarith
    exact hbound.trans (mul_le_mul_of_nonneg_left hpow hCpos.le)
  have hlarge (p e : ℕ) (hp : N ≤ p) :
      (e : ℝ) + 1 ≤ ((p : ℝ) ^ ε) ^ e := by
    have hpR : ((2 : ℝ) ^ ε⁻¹) ≤ p :=
      hN.le.trans (by exact_mod_cast hp)
    have hbase : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc
        2 = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
          (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
        _ ≤ (p : ℝ) ^ ε :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hpR hε.le
    have he : e + 1 ≤ 2 ^ e := by
      have := e.lt_two_pow_self
      omega
    have heR : (e : ℝ) + 1 ≤ (2 : ℝ) ^ e := by exact_mod_cast he
    exact heR.trans (pow_le_pow_left₀ (by norm_num) hbase e)
  refine ⟨C ^ N, pow_pos hCpos _, ?_⟩
  intro n hn
  let s := n.primeFactors
  have hprod : (n.divisors.card : ℝ) ≤
      (∏ p ∈ s, if p < N then C else 1) *
        ∏ p ∈ s, ((p : ℝ) ^ ε) ^ n.factorization p := by
    rw [Nat.card_divisors hn, Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro p hp
      positivity
    · intro p hp
      by_cases hpN : p < N
      · simpa only [ite_eq_left hpN, Nat.cast_add, Nat.cast_one] using
          hsmall p (n.factorization p) (Nat.prime_of_mem_primeFactors hp).two_le
      · simpa only [ite_eq_right hpN, one_mul, Nat.cast_add, Nat.cast_one] using
          hlarge p (n.factorization p) (Nat.le_of_not_gt hpN)
  have hconst : (∏ p ∈ s, if p < N then C else 1) ≤ C ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    apply pow_le_pow_right₀ hC
    calc
      (s.filter (fun p => p < N)).card ≤ (Finset.range N).card :=
        Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = N := Finset.card_range N
  have hpower : (∏ p ∈ s, ((p : ℝ) ^ ε) ^ n.factorization p) = (n : ℝ) ^ ε := by
    calc
      _ = ∏ p ∈ s, ((p : ℝ) ^ n.factorization p) ^ ε := by
        apply Finset.prod_congr rfl
        intro p hp
        calc
          _ = (p : ℝ) ^ (ε * (n.factorization p : ℝ)) :=
            (Real.rpow_mul_natCast (Nat.cast_nonneg p) ε _).symm
          _ = (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by rw [mul_comm ε]
          _ = _ := Real.rpow_natCast_mul (Nat.cast_nonneg p) _ ε
      _ = (∏ p ∈ s, (p : ℝ) ^ n.factorization p) ^ ε :=
        Real.finsetProd_rpow s _ (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) ε
      _ = (n : ℝ) ^ ε := by
        have hfactor : (∏ p ∈ s, (p : ℝ) ^ n.factorization p) = n := by
          exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
        rw [hfactor]
  rw [hpower] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (Nat.cast_nonneg n) ε))

end D5.S3.Arith.Divisors.DivisorSubpower
