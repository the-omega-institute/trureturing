/- GID: D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DivisorCountPrimeFactorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc]
   utility: none
   digest: The divisor count dominates the prime-factor-count correction in A328959. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ArithmeticFunction.Omega ArithmeticFunction.omega

namespace D5.S3.Arith.Congruence.DivisorCountPrimeFactorBound

/-- OEIS A328959, retaining the entry's notation: `cardFactors` is its `omega`
(prime factors with multiplicity), while `cardDistinctFactors` is its `nu`. -/
def a (n : ℕ) : ℤ :=
  (ArithmeticFunction.sigma 0 n : ℤ) - 2 -
    ((ArithmeticFunction.cardFactors n : ℤ) - 1) *
      (ArithmeticFunction.cardDistinctFactors n : ℤ)

/-- Gus Wiseman's OEIS A328959 conjecture: apart from `a(1) = -1`, every term
is nonnegative. -/
theorem wiseman_a328959 : ∀ n : ℕ, 2 ≤ n → 0 ≤ a n := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hexponent (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p := by
    obtain ⟨hpprime, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
    exact hpprime.factorization_pos_of_dvd hn0 hpdvd
  have product_linear_bound : ∀ (s : Finset ℕ) (b : ℕ → ℕ),
      2 ^ s.card + 2 ^ (s.card - 1) * ∑ i ∈ s, b i ≤
        ∏ i ∈ s, (2 + b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro b
        simp
    | @insert x s hx ih =>
        intro b
        by_cases hs : s = ∅
        · subst s
          simp
        · have hscard : 1 ≤ s.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
          have hpow : 2 ^ s.card = 2 * 2 ^ (s.card - 1) := by
            calc
              2 ^ s.card = 2 ^ ((s.card - 1) + 1) := by congr 1; omega
              _ = 2 ^ (s.card - 1) * 2 := by rw [pow_succ]
              _ = 2 * 2 ^ (s.card - 1) := by ac_rfl
          have hmul := Nat.mul_le_mul_right (2 + b x) (ih b)
          rw [Finset.card_insert_of_notMem hx, Finset.sum_insert hx,
            Finset.prod_insert hx, Nat.add_sub_cancel, pow_succ]
          calc
            2 ^ s.card * 2 + 2 ^ s.card * (b x + ∑ i ∈ s, b i) ≤
                (2 ^ s.card + 2 ^ (s.card - 1) * ∑ i ∈ s, b i) *
                  (2 + b x) := by
              rw [hpow]
              nlinarith [Nat.zero_le (2 ^ (s.card - 1) * (∑ i ∈ s, b i) * b x)]
            _ ≤ (∏ i ∈ s, (2 + b i)) * (2 + b x) := hmul
            _ = (2 + b x) * ∏ i ∈ s, (2 + b i) := by ac_rfl
  let r := n.primeFactors.card
  let B := ∑ p ∈ n.primeFactors, (n.factorization p - 1)
  have homega : ArithmeticFunction.cardDistinctFactors n = r := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  have hrpos : 1 ≤ r := by
    rw [← homega]
    exact ArithmeticFunction.cardDistinctFactors_pos.mpr hn
  have hsum : ArithmeticFunction.cardFactors n = r + B := by
    calc
      ArithmeticFunction.cardFactors n =
          ∑ p ∈ n.primeFactors, n.factorization p := by
        rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum,
          Nat.support_factorization]
      _ = ∑ p ∈ n.primeFactors, (1 + (n.factorization p - 1)) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (Nat.add_sub_of_le (hexponent p hp)).symm
      _ = r + B := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul,
          mul_one, r, B]
  have hdivisors :
      2 ^ r + 2 ^ (r - 1) * B ≤ n.divisors.card := by
    calc
      2 ^ r + 2 ^ (r - 1) * B ≤
          ∏ p ∈ n.primeFactors, (2 + (n.factorization p - 1)) :=
        product_linear_bound n.primeFactors (fun p ↦ n.factorization p - 1)
      _ = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        have := hexponent p hp
        omega
      _ = n.divisors.card := (Nat.card_divisors hn0).symm
  have hlinear_pow : ∀ k : ℕ, k + 1 ≤ 2 ^ k :=
    fun k ↦ Nat.succ_le_of_lt Nat.lt_two_pow_self
  have hrpow : r ≤ 2 ^ (r - 1) := by
    have hr : r - 1 + 1 = r := by omega
    simpa only [hr] using hlinear_pow (r - 1)
  have hquadratic_pow_shift : ∀ k : ℕ, 2 + (k + 2) * (k + 1) ≤ 2 ^ (k + 2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [show Nat.succ k + 2 = (k + 2) + 1 by omega, pow_succ]
        nlinarith [Nat.zero_le (k * k)]
  have hquadratic_pow : 2 + r * (r - 1) ≤ 2 ^ r := by
    by_cases hrone : r = 1
    · simp [hrone]
    · have hrtwo : 2 ≤ r := by omega
      have hrdecomp : r = (r - 2) + 2 := by omega
      rw [hrdecomp]
      have hpred : (r - 2 + 2) - 1 = r - 2 + 1 := by omega
      rw [hpred]
      exact hquadratic_pow_shift (r - 2)
  have hnat :
      2 + (ArithmeticFunction.cardFactors n - 1) *
          ArithmeticFunction.cardDistinctFactors n ≤
        ArithmeticFunction.sigma 0 n := by
    rw [ArithmeticFunction.sigma_zero_apply, homega, hsum]
    have hsub : r + B - 1 = (r - 1) + B := by omega
    rw [hsub, Nat.add_mul]
    calc
      2 + ((r - 1) * r + B * r) = (2 + r * (r - 1)) + r * B := by ac_rfl
      _ ≤ 2 ^ r + 2 ^ (r - 1) * B :=
        Nat.add_le_add hquadratic_pow (Nat.mul_le_mul_right B hrpow)
      _ ≤ n.divisors.card := hdivisors
  have hOmega : 1 ≤ ArithmeticFunction.cardFactors n := by omega
  have hcast := Int.ofNat_le.mpr hnat
  push_cast [Nat.cast_sub hOmega] at hcast
  unfold a
  omega

#print axioms wiseman_a328959

end D5.S3.Arith.Congruence.DivisorCountPrimeFactorBound
