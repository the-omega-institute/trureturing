/- GID: D5/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DigitHankel/CyclotomicDigitHankelValuation
   mirror-E: none(waiver:cyclotomic-torsion-valuation)
   anchors: [mathlib/module/Mathlib.RingTheory.Valuation.Basic]
   utility: none
   digest: Torsion roots satisfy a sharp two-adic separation bound. -/

import D5.S3.Combinatorics.DigitHankel.BinaryDigitHankelRecurrence
import Mathlib.RingTheory.Valuation.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelValuation

/-- The nearest nontrivial torsion root to one is minus one in a valuation above two. -/
theorem torsion_root_difference {K Γ : Type*} [Field K] [CharZero K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (htwo : v (2 : K) < 1)
    (n : ℕ) (hn : 0 < n) (ξ : K) (hpow : ξ ^ n = 1) (hne : ξ ≠ 1) :
    v (2 : K) ≤ v (ξ - 1) ∧ (v (ξ - 1) = v (2 : K) ↔ ξ = -1) := by
  have htwo_pos : 0 < v (2 : K) := (v.pos_iff).2 (by norm_num)
  have nat_bound : ∀ m : ℕ, v (m : K) ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      simpa only [Nat.cast_add, Nat.cast_one, map_one] using v.map_add_le ih (by simp)
  have odd_unit : ∀ m : ℕ, Odd m → v (m : K) = 1 := by
    intro m hm
    obtain ⟨j, rfl⟩ := hm
    have hj : v (2 * (j : K)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_right zero_le (nat_bound j)).trans_lt htwo
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, map_one] using
      v.map_add_eq_of_lt_right (x := 2 * (j : K)) (y := 1) (by simpa using hj)
  induction n using Nat.strong_induction_on generalizing ξ with
  | h n ih =>
    by_cases hneg : ξ = -1
    · subst ξ
      have hv : v ((-1 : K) - 1) = v (2 : K) := by
        have heq : (-1 : K) - 1 = -(2 : K) := by ring
        rw [heq, v.map_neg]
      exact ⟨hv.ge, by simp [hv]⟩
    have hstrict : v (2 : K) < v (ξ - 1) := by
      by_contra hnot
      have hsmall : v (ξ - 1) ≤ v (2 : K) := le_of_not_gt hnot
      have hsmall_one : v (ξ - 1) < 1 := hsmall.trans_lt htwo
      have hunit : v ξ = 1 := by
        have : v ξ ^ n = 1 := by rw [← v.map_pow, hpow, map_one]
        exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').1 this
      rcases Nat.even_or_odd n with heven | hodd
      · obtain ⟨m, hm⟩ := heven
        have hm_pos : 0 < m := by omega
        have hm_lt : m < n := by omega
        have hsquare : ξ ^ 2 ≠ 1 := by
          intro hs
          have hfactor : (ξ - 1) * (ξ + 1) = 0 := by
            calc
              (ξ - 1) * (ξ + 1) = ξ ^ 2 - 1 := by ring
              _ = 0 := by rw [hs]; ring
          rcases mul_eq_zero.mp hfactor with hfirst | hlast
          · exact hne (sub_eq_zero.mp hfirst)
          · exact hneg (eq_neg_of_add_eq_zero_left hlast)
        have hsquare_pow : (ξ ^ 2) ^ m = 1 := by
          rw [← pow_mul]
          have hindex : 2 * m = n := by omega
          rw [hindex]
          exact hpow
        have hlower := (ih m hm_lt hm_pos (ξ ^ 2) hsquare_pow hsquare).1
        have hplus : v (ξ + 1) ≤ v (2 : K) := by
          have heq : ξ + 1 = (ξ - 1) + 2 := by ring
          rw [heq]
          exact v.map_add_le hsmall le_rfl
        have hsquare_small : v (ξ ^ 2 - 1) < v (2 : K) := by
          have heq : ξ ^ 2 - 1 = (ξ - 1) * (ξ + 1) := by ring
          rw [heq, map_mul]
          calc
            v (ξ - 1) * v (ξ + 1) ≤ v (2 : K) * v (2 : K) :=
              mul_le_mul hsmall hplus zero_le zero_le
            _ < v (2 : K) := mul_lt_of_lt_one_right htwo_pos htwo
        exact (not_lt_of_ge hlower) hsquare_small
      · have hpowers : ∀ j : ℕ, v (ξ ^ j - 1) ≤ v (ξ - 1) := by
          intro j
          induction j with
          | zero => simp
          | succ j hj =>
            have heq : ξ ^ (j + 1) - 1 = (ξ ^ j - 1) * ξ + (ξ - 1) := by
              rw [pow_succ]; ring
            rw [heq]
            apply v.map_add_le _ le_rfl
            simpa only [map_mul, hunit, mul_one] using hj
        have hsum_small :
            v ((∑ j ∈ Finset.range n, ξ ^ j) - (n : K)) < 1 := by
          have heq : (∑ j ∈ Finset.range n, ξ ^ j) - (n : K) =
              ∑ j ∈ Finset.range n, (ξ ^ j - 1) := by
            rw [Finset.sum_sub_distrib]
            simp
          rw [heq]
          exact (v.map_sum_le fun j _ => hpowers j).trans_lt hsmall_one
        have hsum_unit : v (∑ j ∈ Finset.range n, ξ ^ j) = 1 := by
          have heq : (∑ j ∈ Finset.range n, ξ ^ j) =
              ((∑ j ∈ Finset.range n, ξ ^ j) - (n : K)) + (n : K) := by ring
          rw [heq, v.map_add_eq_of_lt_right]
          · exact odd_unit n hodd
          · simpa only [odd_unit n hodd] using hsum_small
        have hsum_zero : (∑ j ∈ Finset.range n, ξ ^ j) = 0 := by
          have hf := geom_sum_mul ξ n
          rw [hpow, sub_self] at hf
          exact (mul_eq_zero.mp hf).resolve_right (sub_ne_zero.mpr hne)
        rw [hsum_zero, map_zero] at hsum_unit
        exact zero_ne_one hsum_unit
    exact ⟨hstrict.le, by simp [hstrict.ne', hneg]⟩

/-- Strong induction controls the ratio, including the two-bit exceptional tie. -/
theorem recursive_noncancellation {K Γ : Type*} [Field K] [CharZero K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (htwo : v (2 : K) < 1)
    (d : ℕ) (hd : 0 < d) (ζ : K) (hz : ζ ^ d = 1)
    (H E : ℕ → ℕ → K)
    (hbase : ∀ a n, 2 ≤ n → n ≤ 4 → E a n ≠ 0 →
      1 ≤ v ((-1) ^ n * H a n / E a n))
    (htie : ∀ a n, 2 ≤ n → n ≤ 4 → E a n ≠ 0 →
      v ((-1) ^ n * H a n / E a n) = 1 →
      ζ ^ a = -1 ∧ ζ ^ 3 = -1 ∧ v (ζ ^ 2 - 1) = 1)
    (hstep : ∀ a n, 5 ≤ n → E a n ≠ 0 →
      ∃ k m c, 2 ≤ k ∧ 2 ^ k < n ∧ n ≤ 2 ^ (k + 1) ∧
        2 ≤ m ∧ m < n ∧ E c m ≠ 0 ∧
        ((2 * n ≤ 3 * 2 ^ k ∧ m = 2 ^ (k + 1) - n + 1 ∧ c = 1) ∨
          (3 * 2 ^ k < 2 * n ∧ m = n - 2 ^ k ∧ c = a + 1)) ∧
        ζ ^ a ≠ 1 ∧
        (-1) ^ n * H a n / E a n =
          (-1) ^ m * H c m / E c m + (2 * ζ) ^ k / (2 * (ζ ^ a - 1))) :
    ∀ a n, 2 ≤ n → E a n ≠ 0 → H a n ≠ 0 ∧
      1 ≤ v ((-1) ^ n * H a n / E a n) := by
  have h2pos : 0 < v (2 : K) := v.pos_iff.mpr (by norm_num)
  have hzu : v ζ = 1 := by
    apply (pow_eq_one_iff_of_nonneg zero_le hd.ne').1
    rw [← v.map_pow, hz, map_one]
  have hzpos : ζ ≠ 0 := (v.ne_zero_iff).1 (by rw [hzu]; exact one_ne_zero)
  have hαpow (a : ℕ) : (ζ ^ a) ^ d = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  intro a n
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    intro hn hE
    have hbound : 1 ≤ v ((-1) ^ n * H a n / E a n) := by
      by_cases hnsmall : n ≤ 4
      · exact hbase a n hn hnsmall hE
      obtain ⟨k, m, c, hk, hlo, hhi, hm, hmn, hEc, hbranch, hphase, hupdate⟩ :=
        hstep a n (by omega) hE
      have hchild := (ih m hmn c hm hEc).2
      have hdiff := (torsion_root_difference v htwo d hd _ (hαpow a) hphase).1
      have hApos : 0 < v (ζ ^ a - 1) := h2pos.trans_le hdiff
      have hadd : v ((2 * ζ) ^ k / (2 * (ζ ^ a - 1))) =
          v (2 : K) ^ k / (v (2 : K) * v (ζ ^ a - 1)) := by
        rw [v.map_div, v.map_pow, map_mul, hzu, mul_one, map_mul]
      have hcoarse : v ((2 * ζ) ^ k / (2 * (ζ ^ a - 1))) ≤ 1 := by
        rw [hadd]
        apply (div_le_one₀ (mul_pos h2pos hApos)).2
        calc
          v (2 : K) ^ k ≤ v (2 : K) ^ 2 :=
            pow_le_pow_of_le_one zero_le htwo.le hk
          _ = v (2 : K) * v (2 : K) := pow_two _
          _ ≤ v (2 : K) * v (ζ ^ a - 1) := mul_le_mul_of_nonneg_left hdiff zero_le
      have hstrict : v ((2 * ζ) ^ k / (2 * (ζ ^ a - 1))) <
          v ((-1) ^ m * H c m / E c m) := by
        by_cases hklarge : 3 ≤ k
        · have hadd_small : v ((2 * ζ) ^ k / (2 * (ζ ^ a - 1))) < 1 := by
            rw [hadd]
            apply (div_lt_one₀ (mul_pos h2pos hApos)).2
            calc
              v (2 : K) ^ k ≤ v (2 : K) ^ 3 :=
                pow_le_pow_of_le_one zero_le htwo.le hklarge
              _ < v (2 : K) ^ 2 := by
                rw [pow_succ]
                exact mul_lt_of_lt_one_right (pow_pos h2pos _) htwo
              _ ≤ v (2 : K) * v (ζ ^ a - 1) := by
                rw [pow_two]
                exact mul_le_mul_of_nonneg_left hdiff zero_le
          exact hadd_small.trans_le hchild
        have hk2 : k = 2 := by omega
        by_cases hchild_one : v ((-1) ^ m * H c m / E c m) = 1
        · have hm4 : m ≤ 4 := by
            rw [hk2] at hlo hhi hbranch
            norm_num at hlo hhi hbranch
            rcases hbranch with h | h <;> omega
          obtain ⟨hcneg, hz3neg, hsquare⟩ := htie c m hm hm4 hEc hchild_one
          have hparent : v (ζ ^ a - 1) = 1 := by
            rcases hbranch with hreflection | hdeletion
            · have hzneg : ζ = -1 := by simpa only [hreflection.2.2, pow_one] using hcneg
              have hsquare_zero : ζ ^ 2 - 1 = 0 := by rw [hzneg]; ring
              rw [hsquare_zero, map_zero] at hsquare
              exact False.elim (zero_ne_one hsquare)
            · have hparent_pow : ζ ^ a = ζ ^ 2 := by
                apply mul_right_cancel₀ hzpos
                calc
                  ζ ^ a * ζ = ζ ^ (a + 1) := (pow_succ ζ a).symm
                  _ = -1 := by simpa only [hdeletion.2.2] using hcneg
                  _ = ζ ^ 3 := hz3neg.symm
                  _ = ζ ^ 2 * ζ := pow_succ ζ 2
              simpa only [hparent_pow] using hsquare
          rw [hchild_one, hadd, hk2, hparent, mul_one, pow_two]
          simpa only [mul_div_cancel_right₀ _ h2pos.ne'] using htwo
        · exact hcoarse.trans_lt (lt_of_le_of_ne hchild (Ne.symm hchild_one))
      rw [hupdate, v.map_add_eq_of_lt_left hstrict]
      exact hchild
    refine ⟨?_, hbound⟩
    intro hzero
    simp only [hzero, mul_zero, zero_div, map_zero] at hbound
    exact not_le_of_gt zero_lt_one hbound

end D5.S3.Combinatorics.DigitHankel.CyclotomicDigitHankelValuation
