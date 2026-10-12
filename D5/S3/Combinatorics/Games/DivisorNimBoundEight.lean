/- GID: D5/S3/Combinatorics/Games/DivisorNimBoundEight
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBoundEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The universal distinguished-heap bound for a heap of size eight. -/

import D5.S3.Combinatorics.Games.DivisorNimBoundSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic

theorem eight_depth_zero {P : Position} (hp : Positive P)
    (hk : HasDepth P 0) (hm : 8 ∈ P) : grundy P ≤ 5 := by
  have hb := reference_bound hp hk (v := 3) (u := 1) (by simpa using hm)
    (by decide) (by decide) (by decide) (by omega)
  norm_num [recurrenceBound, oddDivisorCount] at hb
  exact hb

theorem eight_depth_one {P : Position} (hp : Positive P)
    (hk : HasDepth P 1) (hm : 8 ∈ P) : grundy P ≤ 10 := by
  have hv8 : valuation 8 = 3 := by
    change valuation (2 ^ 3) = 3
    exact padicValNat.prime_pow 3
  by_cases hc : countAt P 1 = 1
  · have hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < 1 →
        grundy (successor P h d) ≤ 6 := by
      intro h hh d hd hlt
      have hdv : valuation d = 0 := by omega
      have hQ := (lower_move hp hk hh hd rfl hlt).1
      rw [hdv] at hQ
      by_cases he : h = 8
      · subst h
        by_cases hd1 : d = 1
        · subst d
          have hpQ := successor_positive hp hh hd
          obtain ⟨he, hall, hcount, _, _⟩ :=
            paired_pivot_structure hp hk hc hh (by rw [hv8]; decide)
          have h7 : 7 ∈ successor P 8 1 := by
            exact successor_mem_remainder (by decide)
          exact seven_bound hpQ h7 hall hcount
        · have hrem : 8 - d ≤ 5 := by
            have hdpos := hd.1
            have hdle := hd.2.1
            by_contra hn
            have hd2 : d = 2 := by omega
            subst d
            norm_num at hdv
          have hsub := valuation_sub_of_lt hd.1 hd.2.1 (by rw [hv8]; omega)
          have hb := coarse_bound (successor_positive hp hh hd) hQ
            (successor_mem_remainder (by omega)) hrem
          norm_num [coarseBound] at hb
          exact hb
      · have hb := eight_depth_zero (successor_positive hp hh hd) hQ
          (reference_survives hm (Ne.symm he))
        omega
    rcases hk.2 with ⟨z, hz, hzk⟩
    have hb := refined_step hp hk hz hzk ({2, 4, 8} : Finset ℕ) hlow (by
      intro d hd hv
      right
      have hn : 8 ≠ z := by intro he; rw [he] at hv8; omega
      have hdv : d ∣ 8 := hd.2.2 8 ((Multiset.mem_erase_of_ne hn).mpr hm)
      have hdm : d ∈ (8 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hdv, by decide⟩
      have hcases : d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
        have hs : (8 : ℕ).divisors = {1, 2, 4, 8} := by decide
        rw [hs] at hdm
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hdm
      rcases hcases with rfl | rfl | rfl | rfl
      · norm_num at hv
      · simp
      · simp
      · simp)
    simpa using hb
  · have hlow := reference_lower hp hk (v := 3) (u := 1) (B := 8)
      (by simpa using hm) (by decide) (by decide) (by omega)
      (by
        intro Q hpQ j hj hQj hmQ
        have hj0 : j = 0 := by omega
        subst j
        have hb := eight_depth_zero hpQ hQj (by simpa using hmQ)
        omega)
      (by
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        norm_num [changedBound])
    have hb := multiple_step hp hk hc hlow
    omega

theorem eight_depth_two {P : Position} (hp : Positive P)
    (hk : HasDepth P 2) (hm : 8 ∈ P) : grundy P ≤ 14 := by
  have hb := reference_step hp hk (v := 3) (u := 1) (B := 11)
    (by simpa using hm) (by decide) (by decide) (by decide)
    (by
      intro Q hpQ j hj hQj hmQ
      have hc : j = 0 ∨ j = 1 := by omega
      rcases hc with rfl | rfl
      · have hb := eight_depth_zero hpQ hQj (by simpa using hmQ)
        omega
      · have hb := eight_depth_one hpQ hQj (by simpa using hmQ)
        omega)
    (by
      intro j hj
      have hc : j = 0 ∨ j = 1 := by omega
      rcases hc with rfl | rfl <;> norm_num [changedBound])
  norm_num [exceptionalCount, oddDivisorCount] at hb
  exact hb

theorem eight_bound {P : Position} (hp : Positive P) (hm : 8 ∈ P) : grundy P ≤ 16 := by
  have hv8 : valuation 8 = 3 := by
    change valuation (2 ^ 3) = 3
    exact padicValNat.prime_pow 3
  have hn : P ≠ 0 := by intro he; simpa [he] using hm
  obtain ⟨k, hk⟩ := exists_depth hn
  have hkle : k ≤ 3 := by have := hk.1 8 hm; omega
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · have hb := eight_depth_zero hp hk hm
    omega
  · have hb := eight_depth_one hp hk hm
    omega
  · have hb := eight_depth_two hp hk hm
    omega
  · have hb := reference_step hp hk (v := 3) (u := 1) (B := 14)
      (by simpa using hm) (by decide) (by decide) (by decide)
      (by
        intro Q hpQ j hj hQj hmQ
        have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hc with rfl | rfl | rfl
        · have hb := eight_depth_zero hpQ hQj (by simpa using hmQ)
          omega
        · have hb := eight_depth_one hpQ hQj (by simpa using hmQ)
          omega
        · exact eight_depth_two hpQ hQj (by simpa using hmQ))
      (by
        intro j hj
        have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hc with rfl | rfl | rfl <;> norm_num [changedBound])
    norm_num [exceptionalCount] at hb
    exact hb

end D5.S3.Combinatorics.Games.DivisorNimGrundy
