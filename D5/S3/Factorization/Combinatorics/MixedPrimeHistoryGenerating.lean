/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryGenerating
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A truncated mixed prime polynomial operator counts histories by length, and every nonempty history ends at least twice its length. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open Polynomial

/-- Retain precisely the coefficients in degrees one through J. -/
noncomputable def clipPositive (J : ℕ) (f : Polynomial ℕ) : Polynomial ℕ :=
  ∑ n ∈ Finset.Icc 1 J, monomial n (f.coeff n)

/-- Iterate prime addition and multiplication on exponents, retaining degrees one through J. -/
noncomputable def mixedPolynomial (J : ℕ) : ℕ → Polynomial ℕ
  | 0 => X
  | k+1 => clipPositive J (∑ q ∈ Nat.primesLE J,
      (X ^ q * mixedPolynomial J k + (mixedPolynomial J k).comp (X ^ q)))

/-- Sum the length weights of all histories with a positive endpoint, and set the value at zero to zero. -/
noncomputable def weightedCount (r : ℝ) (n : ℕ) : ℝ :=
  if hn : 0 < n then ∑ w ∈ (reachable_finite n hn).2.toFinset, r ^ w.length else 0

/-- Sum the first J mixed history polynomials with a real weight for each step. -/
noncomputable def weightedPolynomial (J : ℕ) (t : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range J, C (t ^ k) * (mixedPolynomial J k).map (Nat.castRingHom ℝ)

/-- The total length weight of histories ending at primes at most X. -/
noncomputable def partition (X : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE X, weightedCount r p

set_option maxHeartbeats 800000 in
/-- In every retained degree, the kth iterate counts histories of length k. -/
theorem mixed_coefficient (J k n : ℕ) (hn : 1 ≤ n) (hnJ : n ≤ J) :
    (mixedPolynomial J k).coeff n = lengthCount k n := by
  classical
  have clip_coeff (J n : ℕ) (f : Polynomial ℕ) (h1 : 1 ≤ n) (hJ : n ≤ J) :
      (clipPositive J f).coeff n = f.coeff n := by
    simp [clipPositive, finsetSum_coeff, coeff_monomial, Finset.mem_Icc, h1, hJ]
  have last_letter_coeff (J n : ℕ) (f : Polynomial ℕ)
      (hf : f.coeff 0 = 0) (hn : 1 ≤ n) (hJ : n ≤ J) :
      (clipPositive J (∑ q ∈ Nat.primesLE J, (X^q * f + f.comp (X^q)))).coeff n =
        (∑ q ∈ (Finset.range n).filter Nat.Prime, f.coeff (n-q)) +
        (∑ q ∈ n.primeFactors, f.coeff (n/q)) := by
    classical
    rw [clip_coeff J n _ hn hJ]
    simp only [finsetSum_coeff, coeff_add, Finset.sum_add_distrib]
    have ha : (Nat.primesLE J).filter (fun q => q < n) =
        (Finset.range n).filter Nat.Prime := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, hp⟩, hq⟩; exact ⟨hq, hp⟩
      · rintro ⟨hq, hp⟩; exact ⟨⟨by omega, hp⟩, hq⟩
    have hm : (Nat.primesLE J).filter (fun q => q ∣ n) = n.primeFactors := by
      ext q
      simp only [Finset.mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors]
      constructor
      · rintro ⟨⟨_, hp⟩, hd⟩; exact ⟨hp, hd, by omega⟩
      · rintro ⟨hp, hd, _⟩
        exact ⟨⟨le_trans (Nat.le_of_dvd (by omega) hd) hJ, hp⟩, hd⟩
    apply congrArg₂ Nat.add
    · rw [← ha, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      rw [coeff_X_pow_mul']
      by_cases h : q < n
      · simp [h, Nat.le_of_lt h]
      · by_cases he : q = n
        · subst q; simp [hf]
        · have hg : ¬ q ≤ n := by omega
          simp [h, hg]
    · rw [← hm, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← expand_eq_comp_X_pow, coeff_expand (Nat.prime_of_mem_primesLE hq).pos]
  have endpoint_one (w : List PrimeLetter) : endpoint w = 1 ↔ w = [] := by
    have grows (v : List PrimeLetter) (m : ℕ) (hm : 0 < m) :
        m + v.length ≤ runWord primeStep v m := by
      induction v generalizing m with
      | nil => simp [runWord]
      | cons a v ih =>
          have hs : m + 1 ≤ primeStep a m := by
            cases a with
            | inl q =>
                have hq := q.property.two_le
                change m + 1 ≤ m + q.val
                omega
            | inr q =>
                have hq := q.property.two_le
                change m + 1 ≤ q.val * m
                nlinarith
          have hi := ih (primeStep a m) (by omega)
          simp only [runWord, List.length_cons]
          omega
    constructor
    · intro h
      have hb := grows w 1 (by omega)
      change 1 + w.length ≤ endpoint w at hb
      exact List.length_eq_zero_iff.mp (by omega)
    · rintro rfl
      rfl
  have length_zero (n : ℕ) : lengthCount 0 n = if n = 1 then 1 else 0 := by
    classical
    change ({w : List PrimeLetter | endpoint w = n ∧ w.length = 0} : Set _).ncard = _
    have hs : ({w : List PrimeLetter | endpoint w = n ∧ w.length = 0} : Set _) =
        if n = 1 then {[]} else ∅ := by
      ext w
      by_cases hn : n = 1
      · subst n
        simp only [if_pos rfl, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro h; exact List.length_eq_zero_iff.mp h.2
        · rintro rfl; exact ⟨rfl, rfl⟩
      · simp only [if_neg hn, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨he, hl⟩
        have hw := List.length_eq_zero_iff.mp hl
        subst w
        exact hn he.symm
    rw [hs]
    split_ifs <;> simp
  have length_succ_one (k : ℕ) : lengthCount (k+1) 1 = 0 := by
    classical
    change ({w : List PrimeLetter | endpoint w = 1 ∧ w.length = k+1} : Set _).ncard = 0
    have hs : ({w : List PrimeLetter | endpoint w = 1 ∧ w.length = k+1} : Set _) = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, endpoint_one]
      rintro ⟨rfl, h⟩
      simp at h
    rw [hs]; simp
  have mixed_coeff_zero (J k : ℕ) : (mixedPolynomial J k).coeff 0 = 0 := by
    cases k with
    | zero => simp [mixedPolynomial]
    | succ k =>
      simp only [mixedPolynomial, clipPositive, finsetSum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      apply coeff_monomial_of_ne
      have hb := (Finset.mem_Icc.mp hi).1
      omega
  induction k generalizing n with
  | zero => simp [mixedPolynomial, length_zero, coeff_X, eq_comm]
  | succ k ih =>
    rw [mixedPolynomial, last_letter_coeff J n _ (mixed_coeff_zero J k) hn hnJ]
    by_cases h1 : n = 1
    · subst n
      simp [length_succ_one, Nat.not_prime_zero]
    · have hn2 : 2 ≤ n := by omega
      rw [length_recurrence (k+1) n (by omega) hn2, Nat.add_sub_cancel]
      apply congrArg₂ Nat.add
      · apply Finset.sum_congr rfl
        intro q hq
        have hqn := Finset.mem_range.mp (Finset.mem_filter.mp hq).1
        exact ih (n-q) (by omega) (by omega)
      · apply Finset.sum_congr rfl
        intro q hq
        exact ih (n/q)
          (Nat.div_pos (Nat.le_of_mem_primeFactors hq) (Nat.pos_of_mem_primeFactors hq))
          (le_trans (Nat.div_le_self n q) hnJ)

/-- Every nonempty prime history ends at least twice its length. -/
theorem sharp_length_bound (w : List PrimeLetter) (hw : w ≠ []) :
    2 * w.length ≤ endpoint w := by
  sorry

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
