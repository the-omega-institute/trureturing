/- GID: D5/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/PrimeFactorSubtractionValueFiniteness
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every positive prime-factor subtraction step difference has a finite fiber. -/

import D5.S3.ArithUnits.CenteredReducedResidueProgressions
import Mathlib.Data.Nat.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.PrimeFactorSubtractionValueFiniteness

open D5.S3.ArithUnits.CenteredReducedResidueProgressions (GreatestPrimeFactor)

/-- The reused largest-factor supremum is attained by a prime divisor. -/
private lemma largestPrimeFactor_mem (n : ℕ) (hn : 2 ≤ n) :
    GreatestPrimeFactor n ∈ n.primeFactors := by
  simpa [GreatestPrimeFactor] using
    Finset.sup_mem_of_nonempty (f := id) (Nat.nonempty_primeFactors.mpr (by omega : 1 < n))

private lemma largest_two_le (n : ℕ) (hn : 2 ≤ n) : 2 ≤ GreatestPrimeFactor n :=
  (Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem n hn)).two_le

/-- Steps to reach `0` by repeatedly subtracting the smallest prime factor (`f` in A399155). -/
def stepsSmallest (n : ℕ) : ℕ :=
  if h : n < 2 then 0 else stepsSmallest (n - n.minFac) + 1
termination_by n
decreasing_by
  exact Nat.sub_lt (by omega) (Nat.minFac_pos n)

/-- Steps to reach `0` by repeatedly subtracting the largest prime factor (`g` in A399155). -/
def stepsLargest (n : ℕ) : ℕ :=
  if h : n < 2 then 0 else stepsLargest (n - GreatestPrimeFactor n) + 1
termination_by n
decreasing_by
  have := largest_two_le n (by omega)
  exact Nat.sub_lt (by omega) (by omega)

/-- A399155: `a(n) = f(n) - g(n)`. -/
def a (n : ℕ) : ℤ := (stepsSmallest n : ℤ) - stepsLargest n

/-- The largest-factor walk spends at least its initial largest prime factor per step. -/
private lemma stepsLargest_mul_largestPrimeFactor_le (n : ℕ) :
    stepsLargest n * GreatestPrimeFactor n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · rw [stepsLargest, dif_pos hn]
      simp
    have hn2 : 2 ≤ n := by omega
    have hmem := largestPrimeFactor_mem n hn2
    have hp := Nat.prime_of_mem_primeFactors hmem
    have hd := Nat.dvd_of_mem_primeFactors hmem
    have hle := Nat.le_of_dvd (by omega : 0 < n) hd
    have hlt : n - GreatestPrimeFactor n < n := Nat.sub_lt (by omega) hp.pos
    have htail : stepsLargest (n - GreatestPrimeFactor n) * GreatestPrimeFactor n ≤
        n - GreatestPrimeFactor n := by
      by_cases hm : n - GreatestPrimeFactor n < 2
      · rw [stepsLargest, dif_pos hm]
        simp
      have hdiv : GreatestPrimeFactor n ∣ n - GreatestPrimeFactor n := Nat.dvd_sub hd (dvd_refl _)
      have hmemtail := hp.mem_primeFactors hdiv (by omega)
      have hmono : GreatestPrimeFactor n ≤ GreatestPrimeFactor (n - GreatestPrimeFactor n) :=
        Finset.le_sup (f := id) hmemtail
      exact (Nat.mul_le_mul_left _ hmono).trans (ih _ hlt)
    rw [stepsLargest, dif_neg hn]
    nlinarith [Nat.sub_add_cancel hle]

/-- On even inputs the smallest-factor walk subtracts two at every step. -/
private lemma stepsSmallest_even (n : ℕ) (hn : 2 ∣ n) : stepsSmallest n = n / 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n < 2
    · rw [stepsSmallest, dif_pos hn2]
      omega
    have hp : n.minFac = 2 := (Nat.minFac_eq_two_iff n).mpr hn
    have hsub : 2 ∣ n - 2 := Nat.dvd_sub hn (dvd_refl _)
    rw [stepsSmallest, dif_neg hn2, hp, ih (n - 2) (by omega) hsub]
    omega

/-- An odd input makes one odd-prime subtraction and then follows the even walk. -/
private lemma stepsSmallest_odd (n : ℕ) (hn : 2 ≤ n) (ho : ¬ 2 ∣ n) :
    stepsSmallest n = 1 + (n - n.minFac) / 2 := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hp2 : n.minFac ≠ 2 := by
    intro h
    exact ho ((Nat.minFac_eq_two_iff n).mp h)
  have hodd := hp.eq_two_or_odd.resolve_left hp2
  have hnodd : n % 2 = 1 := by omega
  have hple : n.minFac ≤ n := Nat.minFac_le (by omega)
  have heven : 2 ∣ n - n.minFac := by omega
  rw [stepsSmallest, dif_neg (by omega), stepsSmallest_even _ heven]
  omega

private lemma largest_three_le_after_two (n : ℕ) (hn : 6 ≤ n) (he : 2 ∣ n)
    (hl : GreatestPrimeFactor n < 3) : 3 ≤ GreatestPrimeFactor (n - 2) := by
  have hhalf : 2 ≤ n / 2 := by omega
  have hp := Nat.minFac_prime (by omega : n / 2 ≠ 1)
  have hdiv : (n / 2).minFac ∣ n :=
    (Nat.minFac_dvd (n / 2)).trans (Nat.div_dvd_of_dvd he)
  have hmem := hp.mem_primeFactors hdiv (by omega)
  have hle : (n / 2).minFac ≤ GreatestPrimeFactor n := Finset.le_sup (f := id) hmem
  have hmin : (n / 2).minFac = 2 := by have := hp.two_le; omega
  have hehalf : 2 ∣ n / 2 := (Nat.minFac_eq_two_iff (n / 2)).mp hmin
  have ht : 3 ≤ (n - 2) / 2 := by omega
  have hot : ¬ 2 ∣ (n - 2) / 2 := by omega
  have hpt := Nat.minFac_prime (by omega : (n - 2) / 2 ≠ 1)
  have hnet : ((n - 2) / 2).minFac ≠ 2 := by
    intro h
    exact hot ((Nat.minFac_eq_two_iff ((n - 2) / 2)).mp h)
  have hdt : ((n - 2) / 2).minFac ∣ n - 2 :=
    (Nat.minFac_dvd ((n - 2) / 2)).trans
      (Nat.div_dvd_of_dvd (Nat.dvd_sub he (dvd_refl 2)))
  have hmt := hpt.mem_primeFactors hdt (by omega)
  have hlt : ((n - 2) / 2).minFac ≤ GreatestPrimeFactor (n - 2) := Finset.le_sup (f := id) hmt
  have := hpt.two_le
  omega

private lemma three_mul_stepsLargest_le (n : ℕ) (hn : 6 ≤ n) :
    3 * stepsLargest n ≤ n + 1 := by
  by_cases hl : 3 ≤ GreatestPrimeFactor n
  · have h := stepsLargest_mul_largestPrimeFactor_le n
    have hm := Nat.mul_le_mul_left (stepsLargest n) hl
    nlinarith
  · have hmem := largestPrimeFactor_mem n (by omega)
    have hp := Nat.prime_of_mem_primeFactors hmem
    have htwo : GreatestPrimeFactor n = 2 := by have := hp.two_le; omega
    have he : 2 ∣ n := htwo ▸ Nat.dvd_of_mem_primeFactors hmem
    have ht := largest_three_le_after_two n hn he (by omega)
    have hb := stepsLargest_mul_largestPrimeFactor_le (n - 2)
    have hm := Nat.mul_le_mul_left (stepsLargest (n - 2)) ht
    rw [stepsLargest, dif_neg (by omega), htwo]
    nlinarith [Nat.sub_add_cancel (show 2 ≤ n by omega)]

private lemma prime_value_zero (n : ℕ) (hn : n.Prime) : a n = 0 := by
  have hl : GreatestPrimeFactor n = n := by simp [GreatestPrimeFactor, hn.primeFactors]
  have hs : stepsSmallest n = 1 := by
    rw [stepsSmallest, dif_neg (by have := hn.two_le; omega), hn.minFac_eq]
    simp only [Nat.sub_self]
    rw [stepsSmallest, dif_pos (by omega)]
  have hg : stepsLargest n = 1 := by
    rw [stepsLargest, dif_neg (by have := hn.two_le; omega), hl]
    simp only [Nat.sub_self]
    rw [stepsLargest, dif_pos (by omega)]
  simp [a, hs, hg]

private lemma composite_lower_bound (n : ℕ) (hn : 6 ≤ n) (hc : ¬ n.Prime) :
    (n : ℤ) ≤ 6 * a n + 3 * (n.sqrt : ℤ) + 3 := by
  have hg := three_mul_stepsLargest_le n hn
  by_cases he : 2 ∣ n
  · have hf := stepsSmallest_even n he
    have hf2 : 2 * stepsSmallest n = n := by rw [hf]; omega
    unfold a
    have hgZ : 3 * (stepsLargest n : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast hg
    have hfZ : 2 * (stepsSmallest n : ℤ) = (n : ℤ) := by exact_mod_cast hf2
    omega
  · have hf := stepsSmallest_odd n (by omega) he
    have hp := Nat.minFac_prime (by omega : n ≠ 1)
    have hne : n.minFac ≠ 2 := by
      intro h
      exact he ((Nat.minFac_eq_two_iff n).mp h)
    have hodd := hp.eq_two_or_odd.resolve_left hne
    have hple := Nat.minFac_le (by omega : 0 < n)
    have hf2 : 2 * stepsSmallest n = n - n.minFac + 2 := by rw [hf]; omega
    have hpS : n.minFac ≤ n.sqrt := Nat.le_sqrt.mpr (by
      simpa [Nat.pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hc)
    have hpZ : (n.minFac : ℤ) ≤ (n.sqrt : ℤ) := by exact_mod_cast hpS
    have hgZ : 3 * (stepsLargest n : ℤ) ≤ (n : ℤ) + 1 := by exact_mod_cast hg
    have hfZ : 2 * (stepsSmallest n : ℤ) = (n : ℤ) - n.minFac + 2 := by
      have heq : 2 * (stepsSmallest n : ℤ) + n.minFac = (n : ℤ) + 2 := by
        exact_mod_cast (show 2 * stepsSmallest n + n.minFac = n + 2 by omega)
      omega
    unfold a
    omega

/-- A399155 observation: each positive value of `a` is attained by only finitely many `n ≥ 2`. -/
def claim : Prop := ∀ v : ℤ, 0 < v → {n : ℕ | 2 ≤ n ∧ a n = v}.Finite

theorem result : claim := by
  intro v hv
  apply (Set.finite_Iic (24 * v.toNat + 21)).subset
  intro n hn
  change n ≤ 24 * v.toNat + 21
  obtain ⟨hn2, hvalue⟩ := hn
  by_cases hn6 : n < 6
  · omega
  have hc : ¬ n.Prime := by
    intro hp
    have hz := prime_value_zero n hp
    omega
  have hb := composite_lower_bound n (by omega) hc
  rw [hvalue] at hb
  have hvn : (v.toNat : ℤ) = v := Int.toNat_of_nonneg (by omega)
  have hbn : n ≤ 6 * v.toNat + 3 * n.sqrt + 3 := by
    exact_mod_cast (show (n : ℤ) ≤ 6 * (v.toNat : ℤ) + 3 * (n.sqrt : ℤ) + 3 by omega)
  have hsq := Nat.sqrt_le n
  have hs : n.sqrt ≤ 6 * v.toNat + 6 := by nlinarith
  omega

end D5.S3.Arith.Primes.PrimeFactorSubtractionValueFiniteness
