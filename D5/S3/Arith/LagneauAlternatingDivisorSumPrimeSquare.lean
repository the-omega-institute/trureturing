/- GID: D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
   generality: G
   mirror-B: D5/B/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Ring.Nat, mathlib/module/Mathlib.Data.Finset.Sort, mathlib/module/Mathlib.Data.Int.ModEq, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Misc, mathlib/module/Mathlib.Tactic.IntervalCases]
   utility: none
   digest: A prime alternating sum of decreasing divisors above three forces a square or twice a square. -/

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.LagneauAlternatingDivisorSumPrimeSquare

open scoped ArithmeticFunction

/-- The alternating sum of all divisors of `n`, in nonincreasing order starting with `n`. -/
def T (n : ℕ) : ℤ :=
  ((n.divisors.sort (· ≥ ·)).map fun d : ℕ ↦ (d : ℤ)).alternatingSum

private theorem alternatingSum_nonneg_of_pairwise_ge :
    ∀ l : List ℕ, l.Pairwise (· ≥ ·) →
      0 ≤ (l.map fun d : ℕ ↦ (d : ℤ)).alternatingSum
  | [], _ => by simp
  | [a], _ => by simp [List.alternatingSum]
  | a :: b :: l, hsorted => by
      simp only [List.pairwise_cons] at hsorted
      have hab : b ≤ a := hsorted.1 b (by simp)
      have htail : l.Pairwise (· ≥ ·) := hsorted.2.2
      have ih := alternatingSum_nonneg_of_pairwise_ge l htail
      change 0 ≤ (a : ℤ) + -(b : ℤ) +
        (l.map fun d : ℕ ↦ (d : ℤ)).alternatingSum
      omega

private theorem le_twice_T (n : ℕ) (hn : 3 < n) : (n : ℤ) ≤ 2 * T n := by
  have hn0 : n ≠ 0 := by omega
  have hsorted :
      n.divisors.sort (· ≥ ·) = n :: n.properDivisors.sort (· ≥ ·) := by
    rw [← Nat.insert_self_properDivisors hn0]
    exact Finset.sort_insert (r := fun a b : ℕ => a ≥ b)
      (fun b hb => (Nat.mem_properDivisors.mp hb).2.le) Nat.self_notMem_properDivisors
  have hproperPairwise :
      (n.properDivisors.sort (· ≥ ·)).Pairwise (· ≥ ·) :=
    Finset.pairwise_sort _ _
  cases hproper : n.properDivisors.sort (· ≥ ·) with
  | nil =>
      have h1 : 1 ∈ n.properDivisors :=
        Nat.mem_properDivisors.mpr ⟨one_dvd n, by omega⟩
      have h1sort : 1 ∈ n.properDivisors.sort (· ≥ ·) :=
        (Finset.mem_sort _).mpr h1
      rw [hproper] at h1sort
      simp at h1sort
  | cons b tail =>
      have hpair : (b :: tail).Pairwise (· ≥ ·) := by
        simpa only [hproper] using hproperPairwise
      have hbSort : b ∈ n.properDivisors.sort (· ≥ ·) := by
        rw [hproper]
        simp
      have hbMem : b ∈ n.properDivisors := (Finset.mem_sort _).mp hbSort
      have hbDiv : b ∣ n := (Nat.mem_properDivisors.mp hbMem).1
      have hbLt : b < n := (Nat.mem_properDivisors.mp hbMem).2
      have hbPos : 0 < b := Nat.pos_of_dvd_of_pos hbDiv (by omega)
      have hquot : 2 ≤ n / b := by
        have hmul : b * (n / b) = n := Nat.mul_div_cancel' hbDiv
        by_contra h
        interval_cases hq : n / b <;> omega
      have htwice : 2 * b ≤ n := by
        calc
          2 * b = b * 2 := by omega
          _ ≤ b * (n / b) := Nat.mul_le_mul_left b hquot
          _ = n := Nat.mul_div_cancel' hbDiv
      have htailNonneg := alternatingSum_nonneg_of_pairwise_ge tail hpair.tail
      rw [T, hsorted, hproper]
      change (n : ℤ) ≤
        2 * ((n : ℤ) + -(b : ℤ) +
          (tail.map fun d : ℕ ↦ (d : ℤ)).alternatingSum)
      have htwice' : (2 : ℤ) * b ≤ n := by exact_mod_cast htwice
      omega

private theorem alternatingSum_modEq_sum :
  ∀ l : List ℤ, l.alternatingSum ≡ l.sum [ZMOD 2]
  | [] => Int.ModEq.rfl
  | [a] => by simp [List.alternatingSum]
  | a :: b :: tail => by
      have hb : -b ≡ b [ZMOD 2] := by
        rw [Int.modEq_iff_dvd]
        exact ⟨b, by ring⟩
      have ha : a ≡ a [ZMOD 2] := Int.ModEq.rfl
      simpa only [List.alternatingSum, List.sum_cons, sub_eq_add_neg, neg_sub, add_assoc] using
        (ha.add hb).add (alternatingSum_modEq_sum tail)

private theorem square_or_twice_square_of_sigma_odd (n : ℕ) (hn0 : n ≠ 0)
    (hsigmaOdd : Odd (ArithmeticFunction.sigma 1 n)) :
    (∃ t : ℕ, n = t ^ 2) ∨ (∃ t : ℕ, n = 2 * t ^ 2) := by
  have hsigmaProd :
      ArithmeticFunction.sigma 1 n =
        ∏ p ∈ n.primeFactors,
          ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i := by
    simpa using
      (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
        (k := 1) hn0)
  have hEvenExponent : ∀ p ∈ n.primeFactors, p ≠ 2 → Even (n.factorization p) := by
    intro p hpMem hpTwo
    have hgeomDvd :
        (∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) ∣
          ArithmeticFunction.sigma 1 n := by
      rw [hsigmaProd]
      exact Finset.dvd_prod_of_mem _ hpMem
    have hgeomOdd := hsigmaOdd.of_dvd_nat hgeomDvd
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hpOdd : Odd p := hpPrime.odd_of_ne_two hpTwo
    rw [Finset.odd_sum_iff_odd_card_odd] at hgeomOdd
    simp only [hpOdd.pow, Finset.filter_true, Finset.card_range] at hgeomOdd
    exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hgeomOdd)
  obtain ⟨k, m, hmOdd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact Nat.not_odd_zero hmOdd
  have hmDivN : m ∣ n := ⟨2 ^ k, by simpa [mul_comm] using hnm⟩
  have hEvenM : ∀ p ∈ m.primeFactors, Even (m.factorization p) := by
    intro p hpMem
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hpDivM : p ∣ m := Nat.dvd_of_mem_primeFactors hpMem
    have hpTwo : p ≠ 2 := by
      intro h
      subst p
      exact hmOdd.not_two_dvd_nat hpDivM
    have hpMemN : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpPrime, hpDivM.trans hmDivN, hn0⟩
    have hpNotDvdTwo : ¬p ∣ 2 := by
      intro hpDivTwo
      exact hpTwo ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpDivTwo)
    have hfactorTwo : (Nat.factorization 2) p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hpNotDvdTwo
    have hnFactor : n.factorization p = m.factorization p := by
      rw [hnm, Nat.factorization_mul (pow_ne_zero _ (by decide)) hm0]
      simp [Nat.factorization_pow, hfactorTwo]
    rw [← hnFactor]
    exact hEvenExponent p hpMemN hpTwo
  let t := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2)
  have hmSquare : m = t ^ 2 := by
    have hprod := Nat.prod_factorization_pow_eq_self hm0
    change (∏ p ∈ m.primeFactors, p ^ m.factorization p) = m at hprod
    rw [← hprod]
    rw [show t = ∏ p ∈ m.primeFactors, p ^ (m.factorization p / 2) by rfl]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hpMem
    obtain ⟨q, hq⟩ := hEvenM p hpMem
    rw [hq]
    have hhalf : (q + q) / 2 = q := by omega
    rw [hhalf]
    simp [pow_add, pow_two]
  rcases Nat.even_or_odd k with hk | hk
  · obtain ⟨j, hj⟩ := hk
    left
    refine ⟨2 ^ j * t, ?_⟩
    rw [hnm, hmSquare, hj]
    simp [pow_add, pow_two]
    ring
  · obtain ⟨j, hj⟩ := hk
    right
    refine ⟨2 ^ j * t, ?_⟩
    rw [hnm, hmSquare, hj]
    simp [pow_succ]
    rw [show 2 ^ (2 * j) = (2 ^ j) ^ 2 by
      rw [show 2 * j = j * 2 by omega, pow_mul]]
    ring

/-- Lagneau's OEIS A193351 conjecture. The alternating sum is integer-valued; for
`n > 3` the proof shows it is nonnegative, so `toNat` preserves its literal value. -/
theorem lagneau_a193351 :
    ∀ n : ℕ, 3 < n → Nat.Prime (T n).toNat →
      (∃ t : ℕ, n = t ^ 2) ∨ (∃ t : ℕ, n = 2 * t ^ 2) := by
  intro n hn hprime
  by_cases hn4 : n = 4
  · subst n
    exact Or.inl ⟨2, by norm_num⟩
  · have hn5 : 5 ≤ n := by omega
    have hbound := le_twice_T n hn
    have hTnonneg : 0 ≤ T n := by omega
    have hTcast : ((T n).toNat : ℤ) = T n := Int.toNat_of_nonneg hTnonneg
    have hTthree : 3 ≤ (T n).toNat := by omega
    have hTodd : Odd (T n).toNat := hprime.odd_of_ne_two (by omega)
    have hsumNat :
        (n.divisors.sort (· ≥ ·)).sum = ∑ d ∈ n.divisors, d := by
      simpa using
        (Finset.sort_perm_toList n.divisors (fun a b : ℕ => a ≥ b)).sum_eq
    have hsumInt :
        ((n.divisors.sort (· ≥ ·)).map (fun d : ℕ ↦ (d : ℤ))).sum =
          (ArithmeticFunction.sigma 1 n : ℤ) := by
      calc
        ((n.divisors.sort (· ≥ ·)).map (fun d : ℕ ↦ (d : ℤ))).sum =
            ((n.divisors.sort (· ≥ ·)).sum : ℤ) := by
          induction n.divisors.sort (· ≥ ·) with
          | nil => rfl
          | cons a tail ih =>
              simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
        _ = ((∑ d ∈ n.divisors, d : ℕ) : ℤ) := by exact_mod_cast hsumNat
        _ = (ArithmeticFunction.sigma 1 n : ℤ) := by
          exact_mod_cast (ArithmeticFunction.sigma_one_apply n).symm
    have hparity : T n ≡ (ArithmeticFunction.sigma 1 n : ℤ) [ZMOD 2] := by
      rw [T, ← hsumInt]
      exact alternatingSum_modEq_sum _
    have hmodInt := hparity.eq
    rw [← hTcast] at hmodInt
    have hmodNat :
        (T n).toNat % 2 = ArithmeticFunction.sigma 1 n % 2 := by
      exact_mod_cast hmodInt
    have hsigmaOdd : Odd (ArithmeticFunction.sigma 1 n) := by
      rw [Nat.odd_iff, ← hmodNat]
      exact Nat.odd_iff.mp hTodd
    exact square_or_twice_square_of_sigma_odd n (by omega) hsigmaOdd

#print axioms T
#print axioms lagneau_a193351

end D5.S3.Arith.LagneauAlternatingDivisorSumPrimeSquare
