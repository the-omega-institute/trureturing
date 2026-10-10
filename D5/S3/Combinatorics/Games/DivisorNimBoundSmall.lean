/- GID: D5/S3/Combinatorics/Games/DivisorNimBoundSmall
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimBoundSmall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The universal bounds for distinguished heaps of sizes two, four, and eight. -/

import D5.S3.Combinatorics.Games.DivisorNimBoundOutcome
import D5.S3.Combinatorics.Games.DivisorNimBoundSmallSupport
import D5.S3.Combinatorics.Games.DivisorNimBoundReference
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.Divisors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

open D5.S3.Combinatorics.Games.DivisorNimBoundArithmetic

theorem refined_step {P : Position} (hp : Positive P) {k B e : ℕ}
    (hk : HasDepth P k) (he : e ∈ P) (hek : valuation e = k) (A : Finset ℕ)
    (hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < k →
      grundy (successor P h d) ≤ B)
    (hhigh : ∀ d, legal P e d → k ≤ valuation d →
      grundy (successor P e d) ≤ B ∨ d ∈ A) :
    grundy P ≤ B + A.card + 1 := by
  classical
  by_cases hg : grundy P = 0
  · omega
  · have hb := grundy_counting P (A.image (successor P e)) B (by
      intro Q hQ
      rcases moves_spec hQ with ⟨h, hh, d, hd, rfl⟩
      by_cases hlt : valuation d < k
      · exact Or.inl (hlow h hh d hd hlt)
      · by_cases hzero : grundy (successor P h d) = 0
        · exact Or.inl (by omega)
        · obtain ⟨hc, hvh⟩ := high_nonzero_unique hp hk hh hd (by omega) hg hzero
          have heh : h = e := unique_min hc hh he hvh hek
          subst h
          rcases hhigh d hd (by omega) with h | h
          · exact Or.inl h
          · exact Or.inr (Finset.mem_image.mpr ⟨d, h, rfl⟩))
    have hc := Finset.card_image_le (s := A) (f := successor P e)
    omega

theorem paired_remainder_zero {P : Position} (hp : Positive P) {h d k : ℕ}
    (hh : h ∈ P) (hd : legal P h d)
    (hothers : ∀ x ∈ P.erase h, k ≤ valuation x)
    (hc : countAt (P.erase h) k = 1) (hr : h - d ≠ 0)
    (hvr : valuation (h - d) = k) : grundy (successor P h d) = 0 := by
  have hdepth : HasDepth (successor P h d) k := by
    refine ⟨?_, h - d, successor_mem_remainder hr, hvr⟩
    intro x hx
    simp only [successor, if_neg hr, Multiset.mem_add, Multiset.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hothers x hx
    · omega
  apply (zero_iff_even_count (successor_positive hp hh hd) hdepth).mpr
  have hcount := countAt_successor (P := P) (h := h) (d := d) (k := k)
  rw [hc, if_pos ⟨hr, hvr⟩] at hcount
  rw [hcount]
  decide

theorem power_divisor_high {d k : ℕ} (hd : d ∣ 2 ^ (k + 1))
    (hk : k ≤ valuation d) : d = 2 ^ k ∨ d = 2 ^ (k + 1) := by
  have hm : d ∈ (2 ^ (k + 1)).divisors :=
    Nat.mem_divisors.mpr ⟨hd, Nat.ne_of_gt (Nat.pow_pos (by decide))⟩
  rcases (Nat.mem_divisors_prime_pow Nat.prime_two (k + 1)).mp hm with ⟨j, hj, rfl⟩
  have hv : valuation (2 ^ j) = j := padicValNat.prime_pow j
  rw [hv] at hk
  have he : j = k ∨ j = k + 1 := by omega
  rcases he with rfl | rfl <;> simp

theorem paired_pivot_bound {P : Position} (hp : Positive P) {k z B : ℕ}
    (hz : z ∈ P) (hzk : valuation z = k)
    (hothers : ∀ x ∈ P.erase z, k + 1 ≤ valuation x)
    (hc : countAt (P.erase z) (k + 1) = 1)
    (hm : 2 ^ (k + 1) ∈ P.erase z)
    (hsub : z - 2 ^ k ≠ 0) (hvsub : valuation (z - 2 ^ k) = k + 1)
    (hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < k →
      grundy (successor P h d) ≤ B) : grundy P ≤ B + 2 := by
  have hk : HasDepth P k := by
    refine ⟨?_, z, hz, hzk⟩
    intro x hx
    by_cases he : x = z
    · subst x; omega
    · exact (Nat.le_succ k).trans
        (hothers x ((Multiset.mem_erase_of_ne he).mpr hx))
  have hb := refined_step hp hk hz hzk ({2 ^ (k + 1)} : Finset ℕ) hlow (by
    intro d hd hdval
    rcases power_divisor_high (hd.2.2 _ hm) hdval with he | he
    · subst d
      left
      have hzero := paired_remainder_zero hp hz hd hothers hc hsub hvsub
      omega
    · exact Or.inr (Finset.mem_singleton.mpr he))
  simpa using hb

theorem lower_paired_bound {P : Position} (hp : Positive P) {h k B : ℕ}
    (hk : HasDepth P (k + 1)) (hc : countAt P (k + 1) = 1)
    (hh : h ∈ P) (hval : k + 1 < valuation h)
    (hm : 2 ^ (k + 1) ∈ P)
    (hlow : ∀ a ∈ successor P h (2 ^ k), ∀ d,
      legal (successor P h (2 ^ k)) a d → valuation d < k →
      grundy (successor (successor P h (2 ^ k)) a d) ≤ B) :
    grundy (successor P h (2 ^ k)) ≤ B + 2 := by
  have hpw : 2 ^ k ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (Nat.le_succ k)
  have hdhi := power_legal hp hk hh
  have hd : legal P h (2 ^ k) :=
    ⟨Nat.pow_pos (by decide),
      (Nat.le_of_dvd (Nat.pow_pos (by decide)) hpw).trans hdhi.2.1,
      fun x hx => hpw.trans (hdhi.2.2 x hx)⟩
  have hvk : valuation (2 ^ k) = k := padicValNat.prime_pow k
  have hsub := valuation_sub_of_lt hd.1 hd.2.1 (by omega)
  obtain ⟨he, hall, hcount, hpositive, hvaluation⟩ :=
    paired_pivot_structure hp hk hc hh hval
  have hn : 2 ^ (k + 1) ≠ h := by
    intro heq
    have ht : valuation (2 ^ (k + 1)) = k + 1 := padicValNat.prime_pow _
    rw [heq] at ht
    omega
  have hm' : 2 ^ (k + 1) ∈ (successor P h (2 ^ k)).erase (h - 2 ^ k) := by
    rw [he]
    exact (Multiset.mem_erase_of_ne hn).mpr hm
  exact paired_pivot_bound (successor_positive hp hh hd)
    (successor_mem_remainder (by omega)) (hsub.2.trans hvk) hall hcount hm'
    (by omega) hvaluation hlow

theorem multiple_step {P : Position} (hp : Positive P) {k B : ℕ}
    (hk : HasDepth P k) (hc : countAt P k ≠ 1)
    (hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < k →
      grundy (successor P h d) ≤ B) : grundy P ≤ B + 1 := by
  by_cases hg : grundy P = 0
  · omega
  · apply grundy_le_of_followers
    intro Q hQ
    rcases moves_spec hQ with ⟨h, hh, d, hd, rfl⟩
    by_cases hl : valuation d < k
    · exact hlow h hh d hd hl
    · by_cases hz : grundy (successor P h d) = 0
      · omega
      · exact False.elim (hc (high_nonzero_unique hp hk hh hd (by omega) hg hz).1)

theorem seven_bound {P : Position} (hp : Positive P) (h7 : 7 ∈ P)
    (hothers : ∀ x ∈ P.erase 7, 1 ≤ valuation x)
    (hc : countAt (P.erase 7) 1 = 1) : grundy P ≤ 6 := by
  have hval7 : valuation 7 = 0 := by norm_num
  have hk : HasDepth P 0 := ⟨fun _ _ => Nat.zero_le _, 7, h7, hval7⟩
  have hz1 : ∀ d, legal P 7 d → d = 1 ∨ d = 5 →
      grundy (successor P 7 d) = 0 := by
    intro d hd hd15
    apply paired_remainder_zero hp h7 hd hothers hc
    · rcases hd15 with rfl | rfl <;> decide
    · rcases hd15 with rfl | rfl
      · exact valuation_eq_of_dvd_not (by decide) (by decide) (by decide)
      · norm_num
  have hb := refined_step hp hk h7 hval7
    ({2, 3, 4, 6, 7} : Finset ℕ) (B := 0)
    (by intro h hh d hd hv; omega) (by
      intro d hd hv
      by_cases he : d = 1 ∨ d = 5
      · exact Or.inl (by rw [hz1 d hd he])
      · right
        have hdpos := hd.1
        have hdle := hd.2.1
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega)
  norm_num at hb
  exact hb

theorem two_bound {P : Position} (hp : Positive P) (hm : 2 ∈ P) : grundy P ≤ 4 := by
  have hv2 : valuation 2 = 1 := by norm_num
  have hn : P ≠ 0 := by intro he; simpa [he] using hm
  obtain ⟨k, hk⟩ := exists_depth hn
  have hkle : k ≤ 1 := by have := hk.1 2 hm; omega
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl
  · have hb := reference_bound hp hk (v := 1) (u := 1) (by simpa using hm)
      (by decide) (by decide) (by decide) (by omega)
    norm_num [recurrenceBound, oddDivisorCount] at hb
    omega
  · by_cases hc : countAt P 1 = 1
    · have hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < 1 →
          grundy (successor P h d) ≤ 2 := by
        intro h hh d hd hdval
        have hdk : valuation d = 0 := by omega
        by_cases he : h = 2
        · subst h
          have hd1 : d = 1 := by
            have hpos := hd.1
            have hle := hd.2.1
            have : d = 1 ∨ d = 2 := by omega
            rcases this with rfl | rfl
            · rfl
            · norm_num at hdk
          subst d
          have hQdepth := (lower_move hp hk hh hd rfl (by norm_num)).1
          have hb := coarse_bound (successor_positive hp hh hd) hQdepth
            (changed_reference (by decide : 1 < 2)) (le_refl 1)
          norm_num [coarseBound] at hb
          exact hb
        · have hdv : d ∣ 2 := hd.2.2 2 ((Multiset.mem_erase_of_ne (Ne.symm he)).mpr hm)
          have hd1 : d = 1 := by
            rcases power_divisor_high (k := 0) (by simpa using hdv) (Nat.zero_le _) with he | he
            · simpa using he
            · subst d; norm_num at hdk
          subst d
          have hval : 1 < valuation h := by
            have hvh := hk.1 h hh
            by_contra hn
            have hvh' : valuation h = 1 := by omega
            exact he (unique_min hc hh hm hvh' hv2)
          simpa using lower_paired_bound hp hk hc hh hval
            (k := 0) (by simpa using hm) (B := 0)
            (by intro a ha d hd hlt; omega)
      have hb := refined_step hp hk hm hv2 ({2} : Finset ℕ) hlow (by
        intro d hd hv
        right
        have hpos := hd.1
        have hle := hd.2.1
        have hd2 : d = 2 := by
          have he : d = 1 ∨ d = 2 := by omega
          rcases he with rfl | rfl
          · norm_num at hv
          · rfl
        exact Finset.mem_singleton.mpr hd2)
      simpa using hb
    · have hlow : ∀ h ∈ P, ∀ d, legal P h d → valuation d < 1 →
          grundy (successor P h d) ≤ 3 := by
        intro h hh d hd hv
        have hdk : valuation d = 0 := by omega
        have hQdepth := (lower_move hp hk hh hd rfl hv).1
        rw [hdk] at hQdepth
        by_cases he : 2 = h
        · subst h
          have hsub := valuation_sub_of_lt hd.1 hd.2.1 (by rw [hv2]; omega)
          have hb := coarse_bound (successor_positive hp hh hd) hQdepth
            (changed_reference (by omega)) (show 2 - d ≤ 2 from Nat.sub_le _ _)
          norm_num [coarseBound] at hb
          exact hb
        · have hb := reference_bound (successor_positive hp hh hd) hQdepth
            (v := 1) (u := 1) (by simpa using reference_survives hm he)
            (by decide) (by decide) (by decide) (by omega)
          norm_num [recurrenceBound, oddDivisorCount] at hb
          exact hb
      exact multiple_step hp hk hc hlow

theorem four_lower_odd {P : Position} (hp : Positive P) {k h d : ℕ}
    (hk : HasDepth P k) (hkpos : 0 < k) (hm : 4 ∈ P)
    (hh : h ∈ P) (hd : legal P h d) (hdval : valuation d = 0) :
    grundy (successor P h d) ≤ 4 := by
  have hQdepth := (lower_move hp hk hh hd rfl (by omega)).1
  rw [hdval] at hQdepth
  by_cases he : 4 = h
  · subst h
    have hsub := valuation_sub_of_lt hd.1 hd.2.1 (by have := hk.1 4 hm; omega)
    have hb := coarse_bound (successor_positive hp hh hd) hQdepth
      (changed_reference (by omega : d < 4)) (show 4 - d ≤ 3 by have := hd.1; omega)
    norm_num [coarseBound] at hb
    exact hb
  · have hb := reference_bound (successor_positive hp hh hd) hQdepth
      (v := 2) (u := 1) (by simpa using reference_survives hm he)
      (by decide) (by decide) (by decide) (by omega)
    norm_num [recurrenceBound, oddDivisorCount] at hb
    exact hb

theorem four_bound {P : Position} (hp : Positive P) (hm : 4 ∈ P) : grundy P ≤ 8 := by
  have hv4 : valuation 4 = 2 := by
    exact valuation_eq_of_dvd_not (by decide) (by decide) (by decide)
  have hn : P ≠ 0 := by intro he; simpa [he] using hm
  obtain ⟨k, hk⟩ := exists_depth hn
  have hkle : k ≤ 2 := by have := hk.1 4 hm; omega
  by_cases hlt : k < 2
  · have hb := reference_bound hp hk (v := 2) (u := 1) (by simpa using hm)
      (by decide) (by decide) (by decide) hkle
    have hmono := recurrenceBound_mono 2 1 (show k ≤ 1 by omega)
    have hval : recurrenceBound 2 1 1 = 7 := by decide
    rw [hval] at hmono
    omega
  · have heq : k = 2 := by omega
    subst k
    have hlow7 : ∀ h ∈ P, ∀ d, legal P h d → valuation d < 2 →
        grundy (successor P h d) ≤ 7 := by
      apply reference_lower hp hk (v := 2) (u := 1) (by simpa using hm)
        (by decide) (by decide) (by omega)
      · intro Q hQp j hj hQj hmQ
        have hb := reference_bound hQp hQj hmQ
          (by decide) (by decide) (by decide) (show j ≤ 2 by omega)
        have hmono := recurrenceBound_mono 2 1 (show j ≤ 1 by omega)
        have hv : recurrenceBound 2 1 1 = 7 := by decide
        rw [hv] at hmono
        omega
      · intro j hj
        have he : j = 0 ∨ j = 1 := by omega
        rcases he with rfl | rfl <;> decide
    by_cases hc : countAt P 2 = 1
    · have hlow6 : ∀ h ∈ P, ∀ d, legal P h d → valuation d < 2 →
          grundy (successor P h d) ≤ 6 := by
        intro h hh d hd hdval
        by_cases he0 : valuation d = 0
        · exact (four_lower_odd hp hk (by decide) hm hh hd he0).trans (by decide)
        · have hd1 : valuation d = 1 := by omega
          by_cases he : h = 4
          · subst h
            have he2 : d = 2 := by
              have hpos := hd.1
              have hle := hd.2.1
              have hcases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
              rcases hcases with rfl | rfl | rfl | rfl
              · norm_num at hd1
              · rfl
              · have hv3 : valuation 3 = 0 :=
                  padicValNat.eq_zero_of_not_dvd (by decide)
                rw [hv3] at hd1
                omega
              · rw [hv4] at hd1; omega
            subst d
            have hb := two_bound (successor_positive hp hh hd)
              (changed_reference (by decide : 2 < 4))
            omega
          · have hdv : d ∣ 4 := hd.2.2 4 ((Multiset.mem_erase_of_ne (Ne.symm he)).mpr hm)
            have he2 : d = 2 := by
              rcases power_divisor_high (k := 1) (by simpa using hdv) (by omega) with ht | ht
              · simpa using ht
              · have ht' : d = 4 := by simpa using ht
                have hvt : valuation (2 ^ (1 + 1)) = 2 := padicValNat.prime_pow _
                rw [ht, hvt] at hd1
                omega
            subst d
            have hval : 2 < valuation h := by
              have hvh := hk.1 h hh
              by_contra hn
              have hvh' : valuation h = 2 := by omega
              exact he (unique_min hc hh hm hvh' hv4)
            have hQdepth := (lower_move hp hk hh hd rfl (by norm_num)).1
            have hmQ := reference_survives hm (Ne.symm he) (d := 2)
            have hb := lower_paired_bound hp hk hc hh hval (k := 1)
              (by simpa using hm) (B := 4) (by
                intro a ha d hd hlt
                apply four_lower_odd (successor_positive hp hh ‹legal P h 2›)
                  hQdepth (by norm_num) hmQ ha hd
                omega)
            exact hb
      have hb := refined_step hp hk hm hv4 ({4} : Finset ℕ) hlow6 (by
        intro d hd hv
        right
        have hpow : 4 ∣ d := by
          exact (Nat.pow_dvd_pow 2 hv).trans pow_padicValNat_dvd
        have hpos := hd.1
        have hle := hd.2.1
        have hge : 4 ≤ d := Nat.le_of_dvd hpos hpow
        exact Finset.mem_singleton.mpr (by omega))
      simpa using hb
    · exact multiple_step hp hk hc hlow7

end D5.S3.Combinatorics.Games.DivisorNimGrundy
