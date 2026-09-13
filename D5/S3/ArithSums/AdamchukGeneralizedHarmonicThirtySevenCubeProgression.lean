/- GID: D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
   generality: G
   mirror-B: D5/B/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
   mirror-E: none(waiver:universal-divisibility-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Field, mathlib/module/Mathlib.Data.Nat.Prime.Factorial, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.LinearCombination, mathlib/module/Mathlib.Tactic.NormNum.NatFactorial, mathlib/module/Mathlib.Tactic.NormNum.Prime, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Cubic divisibility of generalized harmonic numerators along Adamchuk's progression. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

open Finset

namespace D5.S3.ArithSums.AdamchukGeneralizedHarmonicThirtySevenCubeProgression

/-- The generalized harmonic sum `H(36, n)` in OEIS A116184. -/
def H (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc 1 (36 : ℕ), (1 : ℚ) / (j : ℚ) ^ n

private def L : ℕ := Nat.factorial 36

private def b (j : ℕ) : ℕ := L / j

private def N (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc 1 36, (b j : ℤ) ^ n

private abbrev R := ZMod (37 ^ 3)

private def C (k : ℕ) : R :=
  ∑ j ∈ Finset.Icc 1 36, (b j : R) ^ 3 * ((b j : R) ^ 36) ^ k

set_option maxRecDepth 100000 in
private lemma C_zero : ∀ k : ℕ, C k = 0 := by
  have hnil (j : ℕ) (hj : j ∈ Finset.Icc 1 36) :
      (((b j : R) ^ 36) - 1) ^ 3 = 0 := by
    simp only [Finset.mem_Icc] at hj
    obtain ⟨hj_lower, hj_upper⟩ := hj
    interval_cases j <;> decide
  have hzero : C 0 = 0 := by
    decide
  have hone : C 1 = 0 := by
    decide
  have htwo : C 2 = 0 := by
    decide
  have hstep (k : ℕ) :
      C (k + 3) = 3 * C (k + 2) - 3 * C (k + 1) + C k := by
    calc
      C (k + 3) = ∑ j ∈ Finset.Icc 1 36,
          (3 * ((b j : R) ^ 3 * ((b j : R) ^ 36) ^ (k + 2)) -
            3 * ((b j : R) ^ 3 * ((b j : R) ^ 36) ^ (k + 1)) +
            (b j : R) ^ 3 * ((b j : R) ^ 36) ^ k) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [pow_add]
              linear_combination
                (b j : R) ^ 3 * ((b j : R) ^ 36) ^ k * hnil j hj
      _ = 3 * C (k + 2) - 3 * C (k + 1) + C k := by
        simp only [C, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk0 : k = 0
      · simpa [hk0] using hzero
      by_cases hk1 : k = 1
      · simpa [hk1] using hone
      by_cases hk2 : k = 2
      · simpa [hk2] using htwo
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 3 := ⟨k - 3, by omega⟩
      calc
        C (m + 3) = 3 * C (m + 2) - 3 * C (m + 1) + C m := hstep m
        _ = 0 := by
          rw [ih (m + 2) (by omega), ih (m + 1) (by omega), ih m (by omega)]
          ring

/-- Adamchuk's conjectured arithmetic progression in OEIS A116184. -/
theorem adamchuk_a116184 :
    ∀ k : ℕ, (37 ^ 3 : ℤ) ∣ (H (3 + 36 * k)).num := by
  intro k
  let n := 3 + 36 * k
  have hNzero : ((N n : ℤ) : R) = 0 := by
    calc
      ((N n : ℤ) : R) = C k := by
        simp only [N, C, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [n]
        rw [pow_add, pow_mul]
      _ = 0 := C_zero k
  have hH (m : ℕ) : H m = (N m : ℚ) / (L : ℚ) ^ m := by
    unfold H
    rw [show (N m : ℚ) = ∑ j ∈ Finset.Icc 1 36, (b j : ℚ) ^ m by
      simp only [N, Int.cast_sum, Int.cast_pow, Int.cast_natCast]]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hjL : j * b j = L := by
      apply Nat.mul_div_cancel'
      exact Nat.dvd_factorial (by omega) (by omega)
    have hj_ne : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    have hb_ne : (b j : ℚ) ≠ 0 := by
      exact_mod_cast (show b j ≠ 0 by
        intro hb
        rw [hb, Nat.mul_zero] at hjL
        norm_num [L] at hjL)
    calc
      (1 : ℚ) / (j : ℚ) ^ m = (b j : ℚ) ^ m / ((j : ℚ) ^ m * (b j : ℚ) ^ m) := by
        field_simp [hj_ne, hb_ne]
      _ = (b j : ℚ) ^ m / (L : ℚ) ^ m := by
        rw [← mul_pow]
        congr 1
        exact congrArg (fun x : ℚ => x ^ m) (by exact_mod_cast hjL)
  have hscale : H n * (L : ℚ) ^ n = (N n : ℚ) := by
    rw [hH]
    field_simp [L]
  have hrat :
      ((H n).num : ℚ) * (L : ℚ) ^ n =
        (N n : ℚ) * ((H n).den : ℚ) := by
    rw [← Rat.mul_den_eq_num (H n)]
    calc
      (H n * (H n).den) * (L : ℚ) ^ n =
          (H n * (L : ℚ) ^ n) * (H n).den := by ring
      _ = (N n : ℚ) * (H n).den := by rw [hscale]
  have hint :
      (H n).num * (L : ℤ) ^ n = N n * ((H n).den : ℤ) := by
    exact_mod_cast hrat
  have hintMod := congrArg (fun z : ℤ => (z : R)) hint
  push_cast at hintMod
  rw [hNzero] at hintMod
  have hunit : IsUnit ((L : ℕ) : R) := by
    have hp : Nat.Prime 37 := by norm_num
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (by norm_num : 0 < 3)]
    rw [L, Nat.Prime.dvd_factorial hp]
    omega
  have hnumzero : (((H n).num : ℤ) : R) = 0 := by
    refine (hunit.pow n).mul_right_cancel ?_
    simpa using hintMod
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hnumzero

#print axioms adamchuk_a116184

end D5.S3.ArithSums.AdamchukGeneralizedHarmonicThirtySevenCubeProgression
