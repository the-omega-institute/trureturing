/- GID: D5/S1/Words/Palindromes/ThueMorseSharpPrefix
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/ThueMorseSharpPrefix
   mirror-E: none(waiver:literal-thue-morse-sharp-prefix)
   anchors: []
   utility: none
   digest: The actual ordinary prefix cost is at most twice the mixed cost, sharply. -/

import D5.S1.Words.Palindromes.ThueMorseAttainment

/-! A sharp comparison of actual ordinary and mixed costs on all zero-start prefixes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.ThueMorse
open D5.S1.Words.Complexity
open D5.S1.Words.Palindromes.PeriodDoubling

/-- The signed binary weight controls ordinary palindromic cost on every literal prefix. -/
theorem prefix_signed_upper (n : ℕ) :
    FridPrefix.PL (factor n 0) ≤ 2 * signedWeight (n : ℤ) := by
  classical
  obtain ⟨hzero, hone, hneg, htri, heven, hodd⟩ := signed_weight_arithmetic
  have adjacent (x : ℤ) : signedWeight x ≤ signedWeight (x + 1) + 1 ∧
      signedWeight (x + 1) ≤ signedWeight x + 1 := by
    have ha := htri x 1
    have hb := htri (x + 1) (-1)
    have hn := hneg 1
    simp only [hone] at ha hn
    rw [show x + 1 + -1 = x by omega, hn] at hb
    exact ⟨hb, ha⟩
  have low (x : ℤ) : signedWeight (4 * x + 1) = signedWeight x + 1 := by
    rw [show 4 * x + 1 = 2 * (2 * x) + 1 by ring, hodd, heven]
    have ho := hodd x
    have ha := adjacent x
    omega
  have high (x : ℤ) : signedWeight (4 * x + 3) = signedWeight (x + 1) + 1 := by
    have h := low (-(x + 1))
    rw [show 4 * (-(x + 1)) + 1 = -(4 * x + 3) by ring, hneg, hneg] at h
    exact h
  have four (m : ℕ) : FridPrefix.PL (factor (4 * m) 0) ≤ FridPrefix.PL (factor m 0) := by
    simpa only [tau_prefix] using tau_pl (factor m 0)
  have step (m : ℕ) :
      FridPrefix.PL (factor (m + 1) 0) ≤ FridPrefix.PL (factor m 0) + 1 ∧
      FridPrefix.PL (factor m 0) ≤ FridPrefix.PL (factor (m + 1) 0) + 1 := by
    have h := FridPrefix.pl_one_letter_lipschitz (factor m 0) (thueMorse m)
    have hc := factor_concat m 0
    simp only [Nat.zero_add] at hc
    rw [← hc] at h
    rw [abs_le] at h
    constructor <;> omega
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      have hp : FridPrefix.PL ([] : List Bool) ≤ 0 :=
        Nat.find_le (show FridPrefix.PalFactors ([] : List Bool) 0 from
          ⟨[], rfl, rfl, by simp⟩)
      simpa only [factor, List.range_zero, List.map_nil, Nat.cast_zero, hzero,
        Nat.mul_zero] using hp
    · let m := n / 4
      have hm : m < n := by dsimp [m]; omega
      have hr : n = 4 * m + n % 4 := by dsimp [m]; omega
      have hi := ih m hm
      have hfour := four m
      have hrange : n % 4 < 4 := Nat.mod_lt _ (by decide)
      interval_cases hres : n % 4
      · have hn4 : n = 4 * m := by omega
        have hw : signedWeight ((4 * m : ℕ) : ℤ) = signedWeight (m : ℤ) := by
          push_cast
          rw [show (4 : ℤ) * m = 2 * (2 * m) by ring, heven, heven]
        rw [hn4, hw]
        omega
      · have hn4 : n = 4 * m + 1 := by omega
        have hs := (step (4 * m)).1
        have hw : signedWeight (n : ℤ) = signedWeight (m : ℤ) + 1 := by
          rw [hn4]; push_cast; exact low (m : ℤ)
        rw [hw]
        rw [hn4]
        omega
      · have hn4 : n = 4 * m + 2 := by omega
        have hm1 : m + 1 < n := by omega
        have hi1 := ih (m + 1) hm1
        have hf1 := four (m + 1)
        have hs0 := (step (4 * m)).1
        have hs1 := (step (4 * m + 1)).1
        have hs2 := (step (4 * m + 2)).2
        have hs3 := (step (4 * m + 3)).2
        have hw : signedWeight (n : ℤ) =
            1 + min (signedWeight (m : ℤ)) (signedWeight ((m + 1 : ℕ) : ℤ)) := by
          rw [hn4]
          push_cast
          rw [show (4 : ℤ) * m + 2 = 2 * (2 * m + 1) by ring, heven, hodd]
        rw [hw, hn4]
        have he : 4 * (m + 1) = 4 * m + 3 + 1 := by omega
        rw [he] at hf1
        have he' : 4 * m + 2 + 1 = 4 * m + 3 := by omega
        rw [he'] at hs2
        have he'' : 4 * m + 1 + 1 = 4 * m + 2 := by omega
        rw [he''] at hs1
        omega
      · have hn4 : n = 4 * m + 3 := by omega
        have hm1 : m + 1 < n := by omega
        have hi1 := ih (m + 1) hm1
        have hf1 := prefix_four_sub_one (m + 1) (by omega)
        have hw : signedWeight (n : ℤ) = signedWeight ((m + 1 : ℕ) : ℤ) + 1 := by
          rw [hn4]; push_cast; exact high (m : ℤ)
        have he : 4 * (m + 1) - 1 = 4 * m + 3 := by omega
        rw [he] at hf1
        rw [hw, hn4]
        omega

/-- The factor-two bound for every positive prefix, attained by the same actual minima. -/
theorem sharp_factor_two_prefix :
    (∀ n : ℕ, 1 ≤ n → FridPrefix.PL (factor n 0) ≤ 2 * combinedLength (factor n 0)) ∧
    (∃ n : ℕ, 1 ≤ n ∧ FridPrefix.PL (factor n 0) = 2 * combinedLength (factor n 0) ∧
      0 < FridPrefix.PL (factor n 0)) := by
  constructor
  · intro n _hn
    have hp := prefix_signed_upper n
    have hc := (combined_prefix_signed_lower n).1
    omega
  · classical
    have word : factor 2 0 = [false, true] := by decide
    have hw : signedWeight (2 : ℤ) = 1 := by
      have h := signed_weight_arithmetic.2.2.2.2.1 1
      norm_num [signed_weight_arithmetic.2.1] at h ⊢
      exact h
    have hp := prefix_signed_upper 2
    have hc := (combined_prefix_signed_lower 2).1
    have hcu : combinedLength (factor 2 0) ≤ 1 := by
      apply Nat.find_le (show MixedFactors (factor 2 0) 1 from ?_)
      refine ⟨[[false, true]], word.symm, rfl, ?_⟩
      intro p hmem
      have he : p = [false, true] := by simpa using hmem
      subst p
      exact ⟨by decide, Or.inr (by decide)⟩
    have hpl : 2 ≤ FridPrefix.PL (factor 2 0) := by
      by_contra hlt
      obtain ⟨ps, hflat, hlen, hpal⟩ :
          FridPrefix.PalFactors (factor 2 0) (FridPrefix.PL (factor 2 0)) := by
        unfold FridPrefix.PL
        exact Nat.find_spec _
      cases ps with
      | nil => simp [word] at hflat
      | cons p ps =>
        have hps : ps = [] := by
          have hh : ps.length = 0 := by simp only [List.length_cons] at hlen; omega
          exact List.length_eq_zero_iff.mp hh
        subst ps
        have he : p = [false, true] := by simpa [word] using hflat
        have hh := (hpal p (by simp)).2.reverse_eq
        rw [he] at hh
        simp at hh
    norm_num [hw] at hp hc
    have hP : FridPrefix.PL (factor 2 0) = 2 := by omega
    have hC : combinedLength (factor 2 0) = 1 := by omega
    refine ⟨2, by decide, ?_, ?_⟩
    · rw [hP, hC]
    · rw [hP]; decide

end D5.S1.Words.Palindromes.ThueMorse

#print axioms D5.S1.Words.Palindromes.ThueMorse.prefix_signed_upper
#print axioms D5.S1.Words.Palindromes.ThueMorse.sharp_factor_two_prefix
