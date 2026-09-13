/- GID: D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
   generality: G
   mirror-B: D5/B/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
   mirror-E: none(waiver:universal-divisibility-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Rat.Lemmas, mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.FieldTheory.Finite.Basic, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Cubic divisibility of generalized harmonic numerators along Adamchuk's progression. -/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

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

end D5.S3.ArithSums.AdamchukGeneralizedHarmonicThirtySevenCubeProgression
