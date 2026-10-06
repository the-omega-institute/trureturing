/- GID: D5/S3/Combinatorics/DigitHankel/BinaryDigitHankel
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/BinaryDigitHankel
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary digit Hankel determinants at minus two have threshold-triple support. -/

import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelNonzero
set_option autoImplicit false
namespace D5.S3.Combinatorics.DigitHankel.BinaryDigitHankel
open BinaryDigitHankelDefs BinaryDigitHankelRecurrence
theorem result : BinaryDigitHankelDefs.claim := by
  have centers := center_evaluations
  have ends := endpoint_evaluations
  intro n hn
  constructor
  · intro h
    by_contra hout
    exact h (zero_direction n hn hout)
  · rintro ⟨k, hk | hk | hk⟩
    · by_cases hkl : 2 ≤ k
      · have heq : n = threshold k - 1 := by omega
        rw [heq, (ends k hkl).1]
        exact neg_ne_zero.mpr (pow_ne_zero _ (by decide))
      · have hb : ∀ k : Fin 2, ∀ n : Fin 4, 2 ≤ n.val →
            n.val + 1 = threshold k.val → hankel n.val (-2) ≠ 0 := by decide
        have hn4 : n < 4 := by
          have hcases : k = 0 ∨ k = 1 := by omega
          rcases hcases with rfl | rfl <;> norm_num [threshold] at hk ⊢ <;> omega
        exact hb ⟨k, by omega⟩ ⟨n, hn4⟩ hn hk
    · rw [hk]
      obtain ⟨he, hh⟩ := centers k
      have hE : endpoint (threshold k) (-2) ≠ 0 := by
        rw [he]
        apply mul_ne_zero <;> exact pow_ne_zero _ (by decide)
      have htwo : (2 : ℤ) ≤ 2 ^ (k + 1) := by
        calc
          2 = (2 : ℤ) ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by decide) (by omega)
      have hc : (2 : ℤ) ^ (k + 1) + (-1) ^ k ≠ 0 := by
        rcases neg_one_pow_eq_or ℤ k with hs | hs <;> rw [hs] <;> omega
      intro hzero
      rw [hzero, mul_zero] at hh
      exact (mul_ne_zero (neg_ne_zero.mpr hc) hE) hh.symm
    · by_cases hkl : 2 ≤ k
      · rw [hk, (ends k hkl).2.1]
        exact pow_ne_zero _ (by decide)
      · have hb : ∀ k : Fin 2, hankel (threshold k.val + 1) (-2) ≠ 0 := by decide
        rw [hk]
        exact hb ⟨k, by omega⟩
end D5.S3.Combinatorics.DigitHankel.BinaryDigitHankel
