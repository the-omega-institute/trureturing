/- GID: D5/S3/Analytic/Polynomial/HermiteSignedModeThreshold
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteSignedModeThreshold
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Unique signed Hermite mode, quadratic threshold and radical floor formula. -/

import D5.S3.Analytic.Polynomial.HermiteSignedMode
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The signed Hermite mode is unique, with an explicit quadratic threshold and floor formula.

admission_basis: escape-witness. proof_shape: content for divisor_ne_fourth (the ratio of adjacent
positive coefficients is never one), weight_lt_succ, rises_iff, floor_eq and result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Polynomial.HermiteSignedModeThreshold

open Finset
open D5.S3.Analytic.Polynomial.HermiteSignedMode

private theorem rises_iff (n r : ℕ) : rises n r ↔ 4 * r ≤ n ∧ 2 * n ≤ (n - 4 * r) ^ 2 + 7 * (n - 4 * r) + 7 := by
  unfold rises divisor fourth
  constructor
  · rintro ⟨h4, hd⟩
    refine ⟨h4, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 4 * r = j := ⟨_, rfl⟩
    rw [hj] at hd ⊢
    have hn : n = j + 4 * r := by omega
    subst hn
    by_contra hlt
    push Not at hlt
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · omega
    · zify [show 1 ≤ 2 * r by omega] at hd hlt
      nlinarith
  · rintro ⟨h4, hq⟩
    refine ⟨h4, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 4 * r = j := ⟨_, rfl⟩
    rw [hj] at hq ⊢
    have hn : n = j + 4 * r := by omega
    subst hn
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · zify [show 1 ≤ 2 * r by omega] at hq ⊢
      nlinarith

private theorem divisor_ne_fourth (r j : ℕ) : divisor (r + 1) ≠ fourth j := by
  unfold divisor fourth
  intro h
  have h' : ((8 * r + 6 : ℕ) : ℤ) ^ 2 = ((j ^ 2 + 5 * j + 5 : ℕ) : ℤ) ^ 2 + 3 := by
    have : (2 * (r + 1) - 1 : ℕ) = 2 * r + 1 := by omega
    rw [this] at h
    have hz : ((16 * (2 * (r + 1)) * (2 * r + 1) : ℕ) : ℤ) = ((j + 1) * (j + 2) * (j + 3) * (j + 4) : ℕ) := by
      exact_mod_cast h
    push_cast at hz ⊢
    nlinarith
  set X : ℤ := ((8 * r + 6 : ℕ) : ℤ)
  set Y : ℤ := ((j ^ 2 + 5 * j + 5 : ℕ) : ℤ)
  have hX : 6 ≤ X := by simp [X]
  have hY : 5 ≤ Y := by simp only [Y]; push_cast; nlinarith [sq_nonneg (j : ℤ)]
  rcases le_or_gt X Y with hle | hlt
  · nlinarith
  · nlinarith

private theorem weight_lt_succ (n r : ℕ) (h : rises n (r + 1)) : weight n r < weight n (r + 1) := by
  have he := adjacent n r h.1
  have hd : (divisor (r + 1) : ℚ) < fourth (n - 4 * (r + 1)) := by
    exact_mod_cast lt_of_le_of_ne h.2 (divisor_ne_fourth r _)
  have hw := weight_pos n r
  have hw1 := weight_pos n (r + 1)
  have hdpos : (0 : ℚ) < divisor (r + 1) := by
    unfold divisor
    have : 0 < 2 * (r + 1) - 1 := by omega
    positivity
  nlinarith

private theorem weight_lt_mode_of_lt (n r : ℕ) (hr : r < mode n) : weight n r < weight n (mode n) := by
  have hm := mode_rises n
  have key : ∀ k, r < k → k ≤ mode n → weight n r < weight n k := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ k ih =>
      intro hrk hk
      have hstep := weight_lt_succ n k (rises_lower hm hk)
      rcases Nat.lt_or_ge r k with h | h
      · exact (ih h (by omega)).trans hstep
      · have : r = k := by omega
        subst this
        exact hstep
  exact key _ hr le_rfl

private theorem coeff_above (n k : ℕ) (hk : n < k) : (physicistsHermite n).coeff k = 0 := by
  classical
  simp only [physicistsHermite, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  exact sum_eq_zero fun i _ => by rw [ite_eq_right_iff]; intro h; omega

private theorem coeff_a_pos (n : ℕ) : 0 < (physicistsHermite n).coeff (a n) := by
  rw [polynomial_coeff n (a n) (Nat.sub_le _ _)]
  change 0 < signedCoeff n (n - 4 * mode n)
  rw [positive_coefficient n (mode n) (mode_rises n).1]
  have := weight_pos n (mode n)
  positivity

private theorem unique_max (n k : ℕ) (hk : k ≠ a n) :
    (physicistsHermite n).coeff k < (physicistsHermite n).coeff (a n) := by
  have hpos := coeff_a_pos n
  rcases Nat.lt_or_ge n k with hnk | hkn
  · rw [coeff_above n k hnk]; exact hpos
  have hm := (mode_rises n).1
  have hval : (physicistsHermite n).coeff (a n) = n.factorial * weight n (mode n) := by
    rw [polynomial_coeff n (a n) (Nat.sub_le _ _)]
    exact positive_coefficient n (mode n) hm
  rw [polynomial_coeff n k hkn]
  rcases coefficient_cases n k with h | ⟨r, hr, hj, hc⟩
  · exact lt_of_le_of_lt h hpos
  · rw [hc, hval]
    have hrm : r ≠ mode n := by
      intro h; apply hk; rw [hj, h]; rfl
    have hf : (0 : ℚ) < n.factorial := by positivity
    rcases Nat.lt_or_gt_of_ne hrm with h | h
    · exact mul_lt_mul_of_pos_left (weight_lt_mode_of_lt n r h) hf
    · exact mul_lt_mul_of_pos_left (weight_lt_mode n r hr h) hf

private theorem isLeast_a (n : ℕ) :
    IsLeast {j : ℕ | j % 4 = n % 4 ∧ 2 * n ≤ j ^ 2 + 7 * j + 7} (a n) := by
  have hm := (rises_iff n (mode n)).1 (mode_rises n)
  refine ⟨⟨by simp only [a]; omega, hm.2⟩, fun j ⟨hj4, hjF⟩ => ?_⟩
  simp only [a]
  rcases Nat.lt_or_ge n j with h | h
  · omega
  · obtain ⟨r, hr⟩ : ∃ r, n - j = 4 * r := ⟨(n - j) / 4, by omega⟩
    have hrises : rises n r := (rises_iff n r).2 ⟨by omega, by rw [show n - 4 * r = j by omega]; exact hjF⟩
    have := le_mode hrises
    omega

private theorem threshold_iff (n j : ℕ) (hj : j % 4 = n % 4) :
    a n ≤ j ↔ 2 * n ≤ j ^ 2 + 7 * j + 7 := by
  obtain ⟨⟨_, hF⟩, hleast⟩ := isLeast_a n
  constructor
  · intro h
    have : a n ^ 2 ≤ j ^ 2 := Nat.pow_le_pow_left h 2
    omega
  · intro h
    exact hleast ⟨hj, h⟩

private theorem floor_eq (n : ℕ) :
    ⌊((2 * n + 7 : ℝ) - √(8 * n + 21)) / 8⌋ = (mode n : ℤ) := by
  have hm := (rises_iff n (mode n)).1 (mode_rises n)
  have hnot : ¬ rises n (mode n + 1) := fun h => by have := le_mode h; omega
  rw [rises_iff] at hnot
  set m := mode n
  obtain ⟨j, hj⟩ : ∃ j, n - 4 * m = j := ⟨_, rfl⟩
  rw [hj] at hm
  have hnj : n = j + 4 * m := by omega
  have hn : (n : ℝ) = j + 4 * m := by exact_mod_cast hnj
  set s := √(8 * (n : ℝ) + 21) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = 8 * n + 21 := Real.sq_sqrt (by positivity)
  rw [Int.floor_eq_iff]
  constructor
  · have hF : (2 * (n : ℝ)) ≤ j ^ 2 + 7 * j + 7 := by exact_mod_cast hm.2
    have hle : s ≤ 2 * j + 7 := by
      by_contra h
      push Not at h
      nlinarith
    rw [le_div_iff₀ (by norm_num)]
    push_cast
    linarith
  · have hlt : 2 * (j : ℝ) - 1 < s := by
      by_cases h4 : 4 * (m + 1) ≤ n
      · have hF : ¬ 2 * n ≤ (n - 4 * (m + 1)) ^ 2 + 7 * (n - 4 * (m + 1)) + 7 := fun h => hnot ⟨h4, h⟩
        obtain ⟨i, hi⟩ : ∃ i, j = i + 4 := ⟨j - 4, by omega⟩
        rw [show n - 4 * (m + 1) = i by omega] at hF
        push Not at hF
        have hF' : (i : ℝ) ^ 2 + 7 * i + 7 < 2 * n := by exact_mod_cast hF
        have hji : (j : ℝ) = i + 4 := by exact_mod_cast hi
        by_contra h
        push Not at h
        nlinarith
      · have hj3 : j ≤ 3 := by omega
        have hjn : j ≤ n := by omega
        have hjr : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
        have hjnr : (j : ℝ) ≤ n := by exact_mod_cast hjn
        have hj0 : (0 : ℝ) ≤ j := by positivity
        by_contra h
        push Not at h
        nlinarith
    rw [div_lt_iff₀ (by norm_num)]
    push_cast
    linarith

/-- Theorem 1 of Ma and Zhang on OEIS A381423: the signed maximum of the physicists' Hermite
coefficients is attained only at `a n`; among `j ≡ n (mod 4)`, `a n ≤ j` exactly when
`j² + 7j + 7 ≥ 2n`, so `a n` is the least such `j`; and `a n = n - 4 ⌊(2n + 7 - √(8n + 21))/8⌋`. -/
theorem result :
    (∀ n k : ℕ, k ≠ a n → (physicistsHermite n).coeff k < (physicistsHermite n).coeff (a n)) ∧
    (∀ n : ℕ, a n % 4 = n % 4 ∧
      ∀ j : ℕ, j % 4 = n % 4 → (a n ≤ j ↔ 2 * n ≤ j ^ 2 + 7 * j + 7)) ∧
    (∀ n : ℕ, (a n : ℤ) = n - 4 * ⌊((2 * n + 7 : ℝ) - √(8 * n + 21)) / 8⌋) := by
  refine ⟨unique_max, fun n => ⟨(isLeast_a n).1.1, threshold_iff n⟩, fun n => ?_⟩
  rw [floor_eq n]
  have := (mode_rises n).1
  simp only [a]
  push_cast [this]
  ring

end D5.S3.Analytic.Polynomial.HermiteSignedModeThreshold
