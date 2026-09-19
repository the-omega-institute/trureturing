/- GID: D5/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform
   generality: G
   mirror-B: D5/B/S3/Weil/Separator/TranslationEnergy/Scalar/Uniform
   mirror-E: none(waiver:exact-rational-and-analytic-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Weil/Separator/TranslationEnergy/Generic/Certificate.full_certificate; instance=D5/S3/Weil/Separator/TranslationEnergy/Unit/Certificate.center_certificate
   digest: Bound the finite rational cutoff enclosure at every requested precision. -/

import D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform

open scoped BigOperators
open D5.S3.Weil.Separator.TranslationEnergy.Scalar.Logistic

private theorem taylor_uniform (q : Rat) (m : Nat) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    let n := 4 * m + 4
    1 ≤ taylorSum q n ∧
    taylorSum q n ≤ positiveTaylorUpper q n ∧
    positiveTaylorUpper q n ≤ 4 ∧
    positiveTaylorUpper q n - taylorSum q n ≤
      2 / (Nat.factorial n : Rat) := by
  let n := 4 * m + 4
  have hn : 0 < n := by dsimp [n]; omega
  have hn4 : 4 ≤ n := by dsimp [n]; omega
  have hs : ∀ i : Nat, 0 ≤ q ^ i / (Nat.factorial i : Rat) := by
    intro i
    exact div_nonneg (pow_nonneg hq0 _) (by positivity)
  have hl : 1 ≤ taylorSum q n := by
    rw [taylorSum, ← Finset.sum_range_add_sum_Ico
      (fun i => q ^ i / (Nat.factorial i : Rat)) (by omega : 1 ≤ n)]
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hs i)
  have hsum : taylorSum q n ≤ 3 := by
    have he : ((taylorSum q n : Rat) : Real) ≤ Real.exp (q : Real) := by
      simpa only [taylorSum, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
        Rat.cast_natCast] using Real.sum_le_exp_of_nonneg
          (show (0 : Real) ≤ (q : Real) by exact_mod_cast hq0) n
    have he1 : Real.exp (q : Real) ≤ Real.exp 1 :=
      Real.exp_le_exp_of_le (by exact_mod_cast hq1)
    exact_mod_cast (he.trans (he1.trans Real.exp_one_lt_three.le))
  have hqpow : q ^ n ≤ 1 := by simpa using pow_le_pow_left₀ hq0 hq1 n
  have hgap0 : 0 ≤ positiveTaylorUpper q n - taylorSum q n := by
    simp only [positiveTaylorUpper, add_sub_cancel_left]
    positivity
  have hgap : positiveTaylorUpper q n - taylorSum q n ≤
      2 / (Nat.factorial n : Rat) := by
    simp only [positiveTaylorUpper, add_sub_cancel_left]
    have hfac : (0 : Rat) < Nat.factorial n := by positivity
    have hnr : (0 : Rat) < n := by exact_mod_cast hn
    apply (div_le_div_iff₀ (mul_pos hfac hnr) hfac).2
    have hnn : (n + 1 : Nat) ≤ 2 * n := by omega
    have hnr2 : (n : Rat) + 1 ≤ 2 * n := by exact_mod_cast hnn
    nlinarith [mul_nonneg (sub_nonneg.mpr hqpow) (show (0 : Rat) ≤ n + 1 by positivity)]
  have hfac2 : (2 : Rat) ≤ Nat.factorial n := by
    have h : (2 : Nat) ≤ Nat.factorial n := by
      calc
        2 = Nat.factorial 2 := by decide
        _ ≤ Nat.factorial n := Nat.factorial_le (by omega)
    exact_mod_cast h
  have hu : positiveTaylorUpper q n ≤ 4 := by
    have : (2 : Rat) / (Nat.factorial n : Rat) ≤ 1 :=
      (div_le_one (by positivity)).2 hfac2
    linarith
  exact ⟨hl, by linarith, hu, hgap⟩

private theorem scaled_uniform (d : Rat) (m : Nat) (hd0 : 0 ≤ d)
    (hdm : d ≤ (m + 1 : Nat)) :
    let box := scaledExpInterval d (m + 1) (4 * m + 4)
    1 ≤ box.1 ∧ box.1 ≤ box.2 ∧
      box.2 - box.1 ≤ (1 / 2 : Rat) ^ m := by
  let q := d / (m + 1 : Nat)
  let n := 4 * m + 4
  have hq0 : 0 ≤ q := div_nonneg hd0 (by positivity)
  have hq1 : q ≤ 1 := (div_le_one (by positivity)).2 hdm
  obtain ⟨hl, hbase, hu, hgap⟩ := taylor_uniform q m hq0 hq1
  have hpow := abs_pow_sub_pow_le (a := positiveTaylorUpper q n)
    (b := taylorSum q n) (n := m + 1)
  have hpow' : (positiveTaylorUpper q n) ^ (m + 1) -
      (taylorSum q n) ^ (m + 1) ≤
      (positiveTaylorUpper q n - taylorSum q n) * (m + 1) * 4 ^ m := by
    have hpu := pow_le_pow_left₀ (by linarith : (0 : Rat) ≤ taylorSum q n) hbase (m + 1)
    have hpbound : (positiveTaylorUpper q n) ^ m ≤ (4 : Rat) ^ m :=
      pow_le_pow_left₀ (by linarith : (0 : Rat) ≤ positiveTaylorUpper q n) hu m
    have hnonneg : 0 ≤ (positiveTaylorUpper q n - taylorSum q n) * (m + 1 : Rat) :=
      mul_nonneg (sub_nonneg.mpr hbase) (by positivity)
    rw [abs_of_nonneg (sub_nonneg.mpr hpu),
      abs_of_nonneg (by linarith : (0 : Rat) ≤ positiveTaylorUpper q n - taylorSum q n),
      abs_of_nonneg (by linarith : (0 : Rat) ≤ positiveTaylorUpper q n),
      abs_of_nonneg (by linarith : (0 : Rat) ≤ taylorSum q n),
      max_eq_left hbase, show m + 1 - 1 = m by omega] at hpow
    exact hpow.trans (by simpa only [Nat.cast_add, Nat.cast_one] using
      (mul_le_mul_of_nonneg_left hpbound hnonneg))
  have hfac : (0 : Rat) < Nat.factorial n := by positivity
  have hfacpow : (2 : Rat) ^ (4 * m + 3) ≤ (Nat.factorial n : Rat) := by
    have h := Nat.factorial_mul_pow_le_factorial (m := 1) (n := 4 * m + 3)
    have hn : (2 : Nat) ^ (4 * m + 3) ≤ Nat.factorial (4 * m + 4) := by
      simpa only [Nat.factorial_one, one_mul,
        show 1 + 1 = (2 : Nat) by omega,
        show 1 + (4 * m + 3) = 4 * m + 4 by omega] using h
    exact_mod_cast hn
  have hscale : (m + 1 : Rat) ≤ 2 ^ m := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := m)))
  have hnum : (2 : Rat) * (m + 1) * 4 ^ m * 2 ^ m ≤
      (2 : Rat) ^ (4 * m + 3) := by
    calc
      (2 : Rat) * (m + 1) * 4 ^ m * 2 ^ m ≤
          2 * 2 ^ m * 4 ^ m * 2 ^ m := by gcongr
      _ = 2 ^ (1 + m + 2 * m + m) := by
        rw [pow_add, pow_add, pow_add, pow_mul]
        norm_num
      _ = 2 ^ (4 * m + 1) := by congr 1; omega
      _ ≤ 2 ^ (4 * m + 3) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
  have hwidth : (2 : Rat) / (Nat.factorial n : Rat) * (m + 1) * 4 ^ m ≤
      (1 / 2 : Rat) ^ m := by
    rw [one_div_pow]
    apply (le_div_iff₀ (pow_pos (by norm_num) m)).2
    calc
      (2 : Rat) / (Nat.factorial n : Rat) * (m + 1) * 4 ^ m * 2 ^ m =
          (2 * (m + 1) * 4 ^ m * 2 ^ m) / (Nat.factorial n : Rat) := by ring
      _ ≤ 1 := (div_le_one hfac).2 (hnum.trans hfacpow)
  change 1 ≤ (taylorSum q n) ^ (m + 1) ∧
    (taylorSum q n) ^ (m + 1) ≤ (positiveTaylorUpper q n) ^ (m + 1) ∧
    (positiveTaylorUpper q n) ^ (m + 1) - (taylorSum q n) ^ (m + 1) ≤
      (1 / 2 : Rat) ^ m
  exact ⟨by simpa using pow_le_pow_left₀ (by norm_num : (0 : Rat) ≤ 1) hl (m + 1),
    pow_le_pow_left₀ (by linarith : (0 : Rat) ≤ taylorSum q n) hbase (m + 1),
    hpow'.trans (by
      calc
        (positiveTaylorUpper q n - taylorSum q n) * (m + 1) * 4 ^ m ≤
            (2 : Rat) / (Nat.factorial n : Rat) * (m + 1) * 4 ^ m := by gcongr
        _ ≤ (1 / 2 : Rat) ^ m := hwidth)⟩

theorem checkCutoffLogistic_all_precision (t : Rat) (m : Nat) :
    checkCutoffLogistic t m (4 * m + 4) = true ∧
    0 ≤ (cutoffLogisticInterval t m (4 * m + 4)).1 ∧
    (cutoffLogisticInterval t m (4 * m + 4)).1 ≤
      (cutoffLogisticInterval t m (4 * m + 4)).2 ∧
    (cutoffLogisticInterval t m (4 * m + 4)).2 ≤ 1 ∧
    (cutoffLogisticInterval t m (4 * m + 4)).2 -
      (cutoffLogisticInterval t m (4 * m + 4)).1 ≤ (1 / 2 : Rat) ^ m := by
  have logistic_uniform (l u : Rat) (hl : 1 ≤ l) (hlu : l ≤ u) :
      let box := logisticImage (l, u)
      0 ≤ box.1 ∧ box.1 ≤ box.2 ∧ box.2 ≤ 1 ∧ box.2 - box.1 ≤ u - l := by
    have hl0 : 0 < l := by linarith
    have hu0 : 0 < u := lt_of_lt_of_le hl0 hlu
    have hld : 0 < 1 + l := by linarith
    have hud : 0 < 1 + u := by linarith
    have hformula (x : Rat) (hx : 0 < x) :
        1 / x / (1 + 1 / x) = 1 / (1 + x) := by
      field_simp
      ring
    dsimp only [logisticImage]
    rw [hformula u hu0, hformula l hl0]
    have hdiff : 1 / (1 + l) - 1 / (1 + u) =
        (u - l) / ((1 + l) * (1 + u)) := by
      field_simp
      ring
    have hden : (1 : Rat) ≤ (1 + l) * (1 + u) := by
      nlinarith [mul_nonneg hl0.le hu0.le]
    have hwidth : (u - l) / ((1 + l) * (1 + u)) ≤ u - l := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hlu) (sub_nonneg.mpr hden)]
    rw [hdiff]
    exact ⟨by positivity, one_div_le_one_div_of_le hld (by linarith),
      by apply (div_le_iff₀ hld).2; nlinarith, hwidth⟩
  by_cases h0 : t ≤ 0
  · simp [checkCutoffLogistic, CutoffLogisticAccepted, cutoffLogisticInterval, h0]
  by_cases h1 : 1 ≤ t
  · simp [checkCutoffLogistic, CutoffLogisticAccepted, cutoffLogisticInterval, h0, h1]
  have ht0 : 0 < t := lt_of_not_ge h0
  have ht1 : t < 1 := lt_of_not_ge h1
  let reflected := 1 / 2 < t
  let u : Rat := if reflected then 1 - t else t
  have hu0 : 0 < u := by
    dsimp [u, reflected]
    split_ifs <;> linarith
  have huh : u ≤ 1 / 2 := by
    dsimp [u, reflected]
    split_ifs <;> linarith
  have hd0 : 0 ≤ logisticDifference u := by
    have hrest : 0 < 1 - u := by linarith
    have hrec := one_div_le_one_div_of_le hu0 (by linarith : u ≤ 1 - u)
    dsimp [logisticDifference]
    linarith
  let base : Rat × Rat := if (m : Rat) ≤ logisticDifference u then
    (0, (1 / 2 : Rat) ^ m) else logisticInterval u (m + 1) (4 * m + 4)
  have hbase : 0 ≤ base.1 ∧ base.1 ≤ base.2 ∧ base.2 ≤ 1 ∧
      base.2 - base.1 ≤ (1 / 2 : Rat) ^ m := by
    by_cases hfar : (m : Rat) ≤ logisticDifference u
    · simp only [base, hfar, if_true]
      exact ⟨le_refl _, pow_nonneg (by norm_num) _,
        pow_le_one₀ (by norm_num) (by norm_num), by simp⟩
    · have hdm : logisticDifference u ≤ (m + 1 : Nat) := by
        have hdlt : logisticDifference u < m := lt_of_not_ge hfar
        exact hdlt.le.trans (by exact_mod_cast Nat.le_succ m)
      obtain ⟨hl, horder, hwidth⟩ := scaled_uniform
        (logisticDifference u) m hd0 hdm
      have hi := logistic_uniform
        (scaledExpInterval (logisticDifference u) (m + 1) (4 * m + 4)).1
        (scaledExpInterval (logisticDifference u) (m + 1) (4 * m + 4)).2 hl horder
      simp only [base, hfar, if_false, logisticInterval] at hi ⊢
      exact ⟨hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.trans hwidth⟩
  have hcore : if (m : Rat) ≤ logisticDifference u then True
      else LogisticAccepted u (m + 1) (4 * m + 4) := by
    by_cases hfar : (m : Rat) ≤ logisticDifference u
    · simp [hfar]
    · simp only [hfar, if_false]
      have hdm : logisticDifference u ≤ (m + 1 : Nat) := by
        have hdlt : logisticDifference u < m := lt_of_not_ge hfar
        exact hdlt.le.trans (by exact_mod_cast Nat.le_succ m)
      obtain ⟨hl, horder, _⟩ := scaled_uniform
        (logisticDifference u) m hd0 hdm
      have hi := logistic_uniform
        (scaledExpInterval (logisticDifference u) (m + 1) (4 * m + 4)).1
        (scaledExpInterval (logisticDifference u) (m + 1) (4 * m + 4)).2 hl horder
      exact ⟨hu0, huh, by omega, by omega, hd0, hdm,
        by linarith, by simpa only [logisticInterval] using hi.2.1⟩
  have hcut : cutoffLogisticInterval t m (4 * m + 4) =
      if reflected then (1 - base.2, 1 - base.1) else base := by
    by_cases hr : reflected
    · have hr' : (2 : Rat)⁻¹ < t := by
        change 1 / 2 < t at hr
        norm_num at hr ⊢
        exact hr
      simp [cutoffLogisticInterval, h0, h1, hr', u, reflected, hr, base]
    · have hr' : ¬(2 : Rat)⁻¹ < t := by
        change ¬1 / 2 < t at hr
        norm_num at hr ⊢
        exact hr
      simp [cutoffLogisticInterval, h0, h1, hr', u, reflected, hr, base]
  have hbounds : 0 ≤ (cutoffLogisticInterval t m (4 * m + 4)).1 ∧
      (cutoffLogisticInterval t m (4 * m + 4)).1 ≤
        (cutoffLogisticInterval t m (4 * m + 4)).2 ∧
      (cutoffLogisticInterval t m (4 * m + 4)).2 ≤ 1 ∧
      (cutoffLogisticInterval t m (4 * m + 4)).2 -
        (cutoffLogisticInterval t m (4 * m + 4)).1 ≤ (1 / 2 : Rat) ^ m := by
    rw [hcut]
    by_cases hr : reflected
    · simp only [hr, if_true]
      rcases hbase with ⟨ha, hb, hc, hd⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · simpa only [hr, if_false] using hbase
  have haccept : CutoffLogisticAccepted t m (4 * m + 4) := by
    simp only [CutoffLogisticAccepted, h0, h1, if_false]
    exact ⟨hcore, hbounds.2.1, hbounds.2.2.2⟩
  exact ⟨decide_eq_true haccept, hbounds⟩

#print axioms checkCutoffLogistic_all_precision

end D5.S3.Weil.Separator.TranslationEnergy.Scalar.Uniform
