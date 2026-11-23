/- GID: D5/S3/Fourier/Concentration/FourthRootMomentRegion
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/FourthRootMomentRegion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify joint Fourier moments of one probability weight on the cyclic group of order four. -/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

open Finset

namespace D5.S3.Fourier.Concentration.FourthRootMomentRegion

noncomputable section

private theorem squared_mode_region (u v : ℝ) :
    (∃ a b c d : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      a + b + c + d = 1 ∧ (a - c) ^ 2 + (b - d) ^ 2 = u ∧
      (a + c - (b + d)) ^ 2 = v) ↔
      0 ≤ v ∧ v ≤ 1 ∧ 0 ≤ u ∧ u ≤ (1 + v) / 2 := by
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, hsum, rfl, rfl⟩
    let e := a + c
    let o := b + d
    have heo : e + o = 1 := by dsimp [e, o]; linarith
    have hparity : (e - o) ^ 2 ≤ 1 := by
      have hm : 0 ≤ e * o := mul_nonneg (add_nonneg ha hc) (add_nonneg hb hd)
      nlinarith [congrArg (fun x : ℝ => x ^ 2) heo]
    have heven : (a - c) ^ 2 ≤ e ^ 2 := by dsimp [e]; nlinarith [mul_nonneg ha hc]
    have hodd : (b - d) ^ 2 ≤ o ^ 2 := by dsimp [o]; nlinarith [mul_nonneg hb hd]
    have hmass : e ^ 2 + o ^ 2 = (1 + (e - o) ^ 2) / 2 := by
      nlinarith [congrArg (fun x : ℝ => x ^ 2) heo]
    exact ⟨sq_nonneg _, hparity, add_nonneg (sq_nonneg _) (sq_nonneg _),
      (add_le_add heven hodd).trans_eq hmass⟩
  · rintro ⟨hv, hv1, hu, huv⟩
    let s := Real.sqrt v
    let e := (1 + s) / 2
    let o := (1 - s) / 2
    have hs : s ^ 2 = v := Real.sq_sqrt hv
    have hs0 : 0 ≤ s := Real.sqrt_nonneg v
    have hs1 : s ≤ 1 := by nlinarith
    have he : 0 ≤ e := by dsimp [e]; linarith
    have ho : 0 ≤ o := by dsimp [o]; linarith
    have hsum : e + o = 1 := by dsimp [e, o]; ring
    have hdiff : e - o = s := by dsimp [e, o]; ring
    let cap := (1 + v) / 2
    have hcap : 0 < cap := by dsimp [cap]; linarith
    have hsq : e ^ 2 + o ^ 2 = cap := by
      dsimp [e, o, cap]
      nlinarith
    let t := Real.sqrt (u / cap)
    have ht : t ^ 2 = u / cap := Real.sq_sqrt (div_nonneg hu hcap.le)
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have ht1 : t ≤ 1 := by
      have h := (div_le_one hcap).mpr huv
      nlinarith
    have hu' : cap * t ^ 2 = u := by
      rw [ht]
      field_simp
    refine ⟨e * (1 + t) / 2, o * (1 + t) / 2, e * (1 - t) / 2, o * (1 - t) / 2,
      by positivity, by positivity, div_nonneg (mul_nonneg he (sub_nonneg.mpr ht1)) (by norm_num),
      div_nonneg (mul_nonneg ho (sub_nonneg.mpr ht1)) (by norm_num), ?_, ?_, ?_⟩
    · linarith [hsum]
    · calc
        _ = (e ^ 2 + o ^ 2) * t ^ 2 := by ring
        _ = u := by rw [hsq, hu']
    · have h : e * (1 + t) / 2 + e * (1 - t) / 2 -
          (o * (1 + t) / 2 + o * (1 - t) / 2) = s := by linarith [hdiff]
      rw [h, hs]

private theorem char_four_one : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  have h := ZMod.stdAddChar_coe (N := 4) 1
  change ZMod.stdAddChar (1 : ZMod 4) = _ at h
  rw [h]
  calc
    Complex.exp _ = Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) := by
      congr 1
      push_cast
      ring
    _ = Complex.I := Complex.exp_pi_div_two_mul_I

private theorem char_four_two : ZMod.stdAddChar (2 : ZMod 4) = -1 := by
  rw [show (2 : ZMod 4) = 1 + 1 by decide, AddChar.map_add_eq_mul, char_four_one]
  rw [← pow_two, Complex.I_sq]

private theorem char_four_three : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  rw [show (3 : ZMod 4) = 2 + 1 by decide, AddChar.map_add_eq_mul, char_four_two,
    char_four_one, neg_one_mul]

private theorem sum_four {M : Type*} [AddCommMonoid M] (f : ZMod 4 → M) :
    (∑ j, f j) = f 0 + f 1 + f 2 + f 3 := by
  have hu : (univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu, sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  ac_rfl

private theorem dft_four_first (w : ZMod 4 → ℝ) :
    ZMod.dft (fun x => (w x : ℂ)) (1 : ZMod 4) =
      ((w 0 - w 2 : ℝ) : ℂ) + ((w 3 - w 1 : ℝ) : ℂ) * Complex.I := by
  rw [ZMod.dft_apply, sum_four]
  simp only [mul_one, neg_zero, show -(1 : ZMod 4) = 3 by decide,
    show -(2 : ZMod 4) = 2 by decide, show -(3 : ZMod 4) = 1 by decide,
    AddChar.map_zero_eq_one, char_four_one, char_four_two, char_four_three, smul_eq_mul,
    Complex.ofReal_sub]
  ring

private theorem dft_four_second (w : ZMod 4 → ℝ) :
    ZMod.dft (fun x => (w x : ℂ)) (2 : ZMod 4) =
      ((w 0 + w 2 - (w 1 + w 3) : ℝ) : ℂ) := by
  rw [ZMod.dft_apply, sum_four]
  simp only [show -(0 * 2 : ZMod 4) = 0 by decide, show -(1 * 2 : ZMod 4) = 2 by decide,
    show -(2 * 2 : ZMod 4) = 0 by decide, show -(3 * 2 : ZMod 4) = 2 by decide,
    AddChar.map_zero_eq_one, char_four_two, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_sub]
  ring

/-- The first two squared Fourier magnitudes of one probability weight range over an exact region. -/
theorem dft_four_squared_region (u v : ℝ) :
    let cap := (1 + v) / 2
    (∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4)‖ ^ 2 = u ∧
      ‖ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4)‖ ^ 2 = v) ↔
        0 ≤ v ∧ v ≤ 1 ∧ 0 ≤ u ∧ u ≤ cap := by
  dsimp only
  have hfirst (w : ZMod 4 → ℝ) :
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4)‖ ^ 2 =
        (w 0 - w 2) ^ 2 + (w 1 - w 3) ^ 2 := by
    rw [dft_four_first, Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hsecond (w : ZMod 4 → ℝ) :
      ‖ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4)‖ ^ 2 =
        (w 0 + w 2 - (w 1 + w 3)) ^ 2 := by
    rw [dft_four_second, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [← squared_mode_region]
  constructor
  · rintro ⟨w, hw, hsum, hu, hv⟩
    exact ⟨w 0, w 1, w 2, w 3, hw 0, hw 1, hw 2, hw 3,
      (sum_four w).symm.trans hsum, (hfirst w).symm.trans hu, (hsecond w).symm.trans hv⟩
  · rintro ⟨a,b,c,d,ha,hb,hc,hd,hsum,hu,hv⟩
    let w : ZMod 4 → ℝ := fun j => if j = 0 then a else if j = 1 then b else if j = 2 then c else d
    have hw (j : ZMod 4) : 0 ≤ w j := by
      dsimp [w]
      split_ifs <;> assumption
    have w0 : w 0 = a := rfl
    have w1 : w 1 = b := rfl
    have w2 : w 2 = c := rfl
    have w3 : w 3 = d := rfl
    refine ⟨w, hw, ?_, ?_, ?_⟩
    · rw [sum_four, w0, w1, w2, w3, hsum]
    · rw [hfirst, w0, w1, w2, w3, hu]
    · rw [hsecond, w0, w1, w2, w3, hv]

private theorem four_actual_first_moment_max (p : ℕ) (hp : p ≠ 0) :
    IsGreatest
      {A : ℝ | ∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        (‖ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4)‖ ^ 2) ^ p = 0 ∧
        (‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4)‖ ^ 2) ^ p = A}
      ((1 / 2 : ℝ) ^ p) := by
  constructor
  · have h := (dft_four_squared_region (1 / 2) 0).mpr (by norm_num)
    obtain ⟨w, hw, hsum, hfirst, hsecond⟩ := h
    exact ⟨w, hw, hsum, by rw [hsecond, zero_pow hp], by rw [hfirst]⟩
  · intro A hA
    obtain ⟨w, hw, hsum, hsecond, hfirst⟩ := hA
    have hsecond' := eq_zero_of_pow_eq_zero hsecond
    have hregion := (dft_four_squared_region _ 0).mp ⟨w, hw, hsum, rfl, hsecond'⟩
    rw [← hfirst]
    exact pow_le_pow_left₀ hregion.2.2.1 (by simpa using hregion.2.2.2) p

private theorem four_relaxed_first_moment_max :
    IsGreatest
      {A : ℝ | 0 ≤ A ∧ ∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        w 1 = w 3 ∧ ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4) = 0 ∧
        ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4) = (A : ℂ)}
      (1 / 2 : ℝ) := by
  constructor
  · refine ⟨by norm_num, ?_⟩
    let w : ZMod 4 → ℝ := fun j => if j = 0 then 1 / 2 else if j = 2 then 0 else 1 / 4
    have w0 : w 0 = 1 / 2 := rfl
    have w1 : w 1 = 1 / 4 := rfl
    have w2 : w 2 = 0 := rfl
    have w3 : w 3 = 1 / 4 := rfl
    refine ⟨w, ?_, ?_, w1.trans w3.symm, ?_, ?_⟩
    · intro j
      dsimp [w]
      split_ifs <;> norm_num
    · norm_num [sum_four, w0, w1, w2, w3]
    · rw [dft_four_second, w0, w1, w2, w3]
      norm_num
    · rw [dft_four_first, w0, w1, w2, w3]
      norm_num
  · intro A hA
    obtain ⟨_, w, hw, hsum, _, hsecond, hfirst⟩ := hA
    rw [sum_four] at hsum
    rw [dft_four_second] at hsecond
    rw [dft_four_first] at hfirst
    have hsecondRe := congrArg Complex.re hsecond
    have hfirstRe := congrArg Complex.re hfirst
    simp [Complex.mul_re] at hfirstRe
    simp at hsecondRe
    linarith [hw 2]

/-- With the second mode zero, the true powered moment and the Fourier-positive
probability relaxation have different maxima for every degree at least two. -/
theorem four_first_moment_maxima (p : ℕ) (hp : 2 ≤ p) :
    let cap := (1 / 2 : ℝ) ^ p
    IsGreatest
      {A : ℝ | ∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        (‖ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4)‖ ^ 2) ^ p = 0 ∧
        (‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4)‖ ^ 2) ^ p = A}
      cap ∧
    IsGreatest
      {A : ℝ | 0 ≤ A ∧ ∃ w : ZMod 4 → ℝ, (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧
        w 1 = w 3 ∧ ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 4) = 0 ∧
        ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 4) = (A : ℂ)}
      (1 / 2 : ℝ) ∧ cap < 1 / 2 := by
  dsimp only
  refine ⟨four_actual_first_moment_max p (by omega), four_relaxed_first_moment_max, ?_⟩
  simpa only [pow_one] using
    pow_lt_pow_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) (show 1 < p by omega)

#print axioms dft_four_squared_region
#print axioms four_first_moment_maxima

end

end D5.S3.Fourier.Concentration.FourthRootMomentRegion
