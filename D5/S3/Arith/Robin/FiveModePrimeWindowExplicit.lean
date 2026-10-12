/- GID: D5/S3/Arith/Robin/FiveModePrimeWindowExplicit
   generality: I
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Arith/Robin/FiveModePrimeWindowBridge, D5/S3/Arith/GoldenResource/GoldenDivisorLanguage]
   utility: none
   digest: Exact normalized five-mode vectors on the finite six-cell at 5040. -/

import D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
import D5.S3.Arith.Robin.FiveModePrimeWindowBridge
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Robin.FiveModePrimeWindowBridge

open scoped BigOperators
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

noncomputable section

/-- The finite six-cell of integer values whose 5040 observation is exact. -/
def sixCell : Finset ℕ := {5040, 10080, 15120, 20160, 30240, 60480}

private theorem factorization_5040_two :
    (5040 : ℕ).factorization 2 = 4 := by
  have h : (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 := by norm_num
  rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  have h16 : (16 : ℕ).factorization 2 = 4 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact Nat.factorization_pow_self Nat.prime_two
  have h9 : (9 : ℕ).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h5 : (5 : ℕ).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h7 : (7 : ℕ).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  norm_num [h16, h9, h5, h7]

private theorem factorization_5040_three :
    (5040 : ℕ).factorization 3 = 2 := by
  have h : (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 := by norm_num
  rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  have h16 : (16 : ℕ).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h9 : (9 : ℕ).factorization 3 = 2 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
    exact Nat.factorization_pow_self Nat.prime_three
  have h5 : (5 : ℕ).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h7 : (7 : ℕ).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  norm_num [h16, h9, h5, h7]

private theorem factorization_5040_five :
    (5040 : ℕ).factorization 5 = 1 := by
  have h : (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 := by norm_num
  rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  have h16 : (16 : ℕ).factorization 5 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h9 : (9 : ℕ).factorization 5 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h5 : (5 : ℕ).factorization 5 = 1 := by
    rw [show (5 : ℕ) = 5 ^ 1 by norm_num]
    exact Nat.factorization_pow_self Nat.prime_five
  have h7 : (7 : ℕ).factorization 5 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  norm_num [h16, h9, h5, h7]

private theorem factorization_5040_seven :
    (5040 : ℕ).factorization 7 = 1 := by
  have h : (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 := by norm_num
  rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  have h16 : (16 : ℕ).factorization 7 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h9 : (9 : ℕ).factorization 7 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h5 : (5 : ℕ).factorization 7 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h7 : (7 : ℕ).factorization 7 = 1 := by
    rw [show (7 : ℕ) = 7 ^ 1 by norm_num]
    exact Nat.factorization_pow_self Nat.prime_seven
  norm_num [h16, h9, h5, h7]

private theorem factorization_5040_eightyThree :
    (5040 : ℕ).factorization 83 = 0 := by
  have h : (5040 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 := by norm_num
  rw [h]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  have h16 : (16 : ℕ).factorization 83 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h9 : (9 : ℕ).factorization 83 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h5 : (5 : ℕ).factorization 83 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  have h7 : (7 : ℕ).factorization 83 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    norm_num
  norm_num [h16, h9, h5, h7]

private theorem cell_factorization_two (u : Fin 3) (v : Fin 2) :
    (5040 * 2 ^ u.val * 3 ^ v.val).factorization 2 = 4 + u.val := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  rw [factorization_5040_two]
  simp [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow,
    Finsupp.single_apply]

private theorem cell_factorization_three (u : Fin 3) (v : Fin 2) :
    (5040 * 2 ^ u.val * 3 ^ v.val).factorization 3 = 2 + v.val := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  rw [factorization_5040_three]
  simp [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow,
    Finsupp.single_apply]

private theorem cell_factorization_five (u : Fin 3) (v : Fin 2) :
    (5040 * 2 ^ u.val * 3 ^ v.val).factorization 5 = 1 := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  rw [factorization_5040_five]
  simp [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow,
    Finsupp.single_apply]

private theorem cell_factorization_seven (u : Fin 3) (v : Fin 2) :
    (5040 * 2 ^ u.val * 3 ^ v.val).factorization 7 = 1 := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  rw [factorization_5040_seven]
  simp [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow,
    Finsupp.single_apply]

private theorem cell_factorization_eightyThree (u : Fin 3) (v : Fin 2) :
    (5040 * 2 ^ u.val * 3 ^ v.val).factorization 83 = 0 := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply]
  rw [factorization_5040_eightyThree]
  simp [Nat.prime_two.factorization_pow, Nat.prime_three.factorization_pow,
    Finsupp.single_apply]

/-- Every member of the 5040 six-cell has an explicit five-prime normalized vector.
The two finite parameters record the extra powers of 2 and 3 above 5040. -/
theorem goldenCell5040_prime_window_explicit_core
    {n : ℕ} (hn : n ∈ sixCell) :
    ∃ u : Fin 3, ∃ v : Fin 2,
      n = 5040 * 2 ^ u.val * 3 ^ v.val ∧
      windowDenom n = (13 + u.val + v.val : ℝ) ∧
      primeWindow n 0 = ((5 + u.val : ℕ) : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 1 = ((3 + v.val : ℕ) : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 2 = (2 : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 3 = (2 : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 4 = (1 : ℝ) / (13 + u.val + v.val) ∧
      visible (primeWindow n) =
        (((4 + v.val : ℕ) : ℝ) / (13 + u.val + v.val),
          (3 : ℝ) / (13 + u.val + v.val),
          (2 : ℝ) / (13 + u.val + v.val)) := by
  have hm0 : modePrimes (0 : Fin 5) = 2 := by decide
  have hm1 : modePrimes (1 : Fin 5) = 3 := by decide
  have hm2 : modePrimes (2 : Fin 5) = 5 := by decide
  have hm3 : modePrimes (3 : Fin 5) = 7 := by decide
  have hm4 : modePrimes (4 : Fin 5) = 83 := by decide
  simp only [sixCell, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ?_⟩
    have h2 := factorization_5040_two
    have h3 := factorization_5040_three
    have h5 := factorization_5040_five
    have h7 := factorization_5040_seven
    have h83 := factorization_5040_eightyThree
    norm_num [windowDenom, primeWindow, visible, Fin.sum_univ_five,
      hm0, hm1, hm2, hm3, hm4, h2, h3, h5, h7, h83]
  · refine ⟨⟨1, by decide⟩, ⟨0, by decide⟩, ?_⟩
    have h2 : (10080 : ℕ).factorization 2 = 5 := by
      convert cell_factorization_two (⟨1, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h3 : (10080 : ℕ).factorization 3 = 2 := by
      convert cell_factorization_three (⟨1, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h5 : (10080 : ℕ).factorization 5 = 1 := by
      convert cell_factorization_five (⟨1, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h7 : (10080 : ℕ).factorization 7 = 1 := by
      convert cell_factorization_seven (⟨1, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h83 : (10080 : ℕ).factorization 83 = 0 := by
      convert cell_factorization_eightyThree (⟨1, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    norm_num [windowDenom, primeWindow, visible, Fin.sum_univ_five,
      hm0, hm1, hm2, hm3, hm4, h2, h3, h5, h7, h83]
  · refine ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
    have h2 : (15120 : ℕ).factorization 2 = 4 := by
      convert cell_factorization_two (⟨0, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h3 : (15120 : ℕ).factorization 3 = 3 := by
      convert cell_factorization_three (⟨0, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h5 : (15120 : ℕ).factorization 5 = 1 := by
      convert cell_factorization_five (⟨0, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h7 : (15120 : ℕ).factorization 7 = 1 := by
      convert cell_factorization_seven (⟨0, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h83 : (15120 : ℕ).factorization 83 = 0 := by
      convert cell_factorization_eightyThree (⟨0, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    norm_num [windowDenom, primeWindow, visible, Fin.sum_univ_five,
      hm0, hm1, hm2, hm3, hm4, h2, h3, h5, h7, h83]
  · refine ⟨⟨2, by decide⟩, ⟨0, by decide⟩, ?_⟩
    have h2 : (20160 : ℕ).factorization 2 = 6 := by
      convert cell_factorization_two (⟨2, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h3 : (20160 : ℕ).factorization 3 = 2 := by
      convert cell_factorization_three (⟨2, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h5 : (20160 : ℕ).factorization 5 = 1 := by
      convert cell_factorization_five (⟨2, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h7 : (20160 : ℕ).factorization 7 = 1 := by
      convert cell_factorization_seven (⟨2, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    have h83 : (20160 : ℕ).factorization 83 = 0 := by
      convert cell_factorization_eightyThree (⟨2, by decide⟩) (⟨0, by decide⟩) using 1 <;> norm_num
    norm_num [windowDenom, primeWindow, visible, Fin.sum_univ_five,
      hm0, hm1, hm2, hm3, hm4, h2, h3, h5, h7, h83]
  · refine ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ?_⟩
    have h2 : (30240 : ℕ).factorization 2 = 5 := by
      convert cell_factorization_two (⟨1, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h3 : (30240 : ℕ).factorization 3 = 3 := by
      convert cell_factorization_three (⟨1, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h5 : (30240 : ℕ).factorization 5 = 1 := by
      convert cell_factorization_five (⟨1, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h7 : (30240 : ℕ).factorization 7 = 1 := by
      convert cell_factorization_seven (⟨1, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h83 : (30240 : ℕ).factorization 83 = 0 := by
      convert cell_factorization_eightyThree (⟨1, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    norm_num [windowDenom, primeWindow, visible, Fin.sum_univ_five,
      hm0, hm1, hm2, hm3, hm4, h2, h3, h5, h7, h83]
  · refine ⟨⟨2, by decide⟩, ⟨1, by decide⟩, ?_⟩
    have h2 : (60480 : ℕ).factorization 2 = 6 := by
      convert cell_factorization_two (⟨2, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h3 : (60480 : ℕ).factorization 3 = 3 := by
      convert cell_factorization_three (⟨2, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h5 : (60480 : ℕ).factorization 5 = 1 := by
      convert cell_factorization_five (⟨2, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h7 : (60480 : ℕ).factorization 7 = 1 := by
      convert cell_factorization_seven (⟨2, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    have h83 : (60480 : ℕ).factorization 83 = 0 := by
      convert cell_factorization_eightyThree (⟨2, by decide⟩) (⟨1, by decide⟩) using 1 <;> norm_num
    norm_num [windowDenom, primeWindow, visible, Fin.sum_univ_five,
      hm0, hm1, hm2, hm3, hm4, h2, h3, h5, h7, h83]

#print axioms goldenCell5040_prime_window_explicit_core

end

end D5.S3.Arith.Robin.FiveModePrimeWindowBridge

namespace D5.S3.Arith.Robin.FiveModePrimeWindowExplicit

open D5.S3.Arith.Robin.FiveModePrimeWindowBridge
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

/-- Source-module alias for the finite explicit six-cell vector theorem. -/
theorem goldenCell5040_prime_window_explicit
    {n : ℕ} (hn : n ∈ sixCell) :
    ∃ u : Fin 3, ∃ v : Fin 2,
      n = 5040 * 2 ^ u.val * 3 ^ v.val ∧
      windowDenom n = (13 + u.val + v.val : ℝ) ∧
      primeWindow n 0 = ((5 + u.val : ℕ) : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 1 = ((3 + v.val : ℕ) : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 2 = (2 : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 3 = (2 : ℝ) / (13 + u.val + v.val) ∧
      primeWindow n 4 = (1 : ℝ) / (13 + u.val + v.val) ∧
      visible (primeWindow n) =
        (((4 + v.val : ℕ) : ℝ) / (13 + u.val + v.val),
          (3 : ℝ) / (13 + u.val + v.val),
          (2 : ℝ) / (13 + u.val + v.val)) :=
  D5.S3.Arith.Robin.FiveModePrimeWindowBridge.goldenCell5040_prime_window_explicit_core hn

#print axioms goldenCell5040_prime_window_explicit

end D5.S3.Arith.Robin.FiveModePrimeWindowExplicit
