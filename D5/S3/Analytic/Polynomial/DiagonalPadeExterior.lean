/- GID: D5/S3/Analytic/Polynomial/DiagonalPadeExterior
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/DiagonalPadeExterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parabolic exclusion and exterior residues for diagonal exponential Padé poles. -/
module

import all D5.S3.Analytic.HalfIntegerBessel
public import D5.S3.Analytic.Polynomial.DiagonalPadeExponential
import all D5.S3.Analytic.Polynomial.DiagonalPadeExponential
public import D5.S3.Analytic.Polynomial.DiagonalPadePhase
import all D5.S3.Analytic.Polynomial.DiagonalPadePhase
public import D5.S3.Analytic.Polynomial.DiagonalPadeResidue
import all D5.S3.Analytic.Polynomial.DiagonalPadeResidue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

public section

open Polynomial Set Metric
open scoped Nat Topology
open D5.S3.Analytic.HalfIntegerBessel (order S eta S_re_pos hasDerivAt_eta sectorMass)
open D5.S3.Analytic.Polynomial.DiagonalPadeExponential
open D5.S3.Analytic.Polynomial.DiagonalPadePhase
open D5.S3.Analytic.Polynomial.DiagonalPadeResidue (centralPole)

namespace D5.S3.Analytic.Polynomial.DiagonalPadeExterior

private noncomputable def reflectedContinuant (m k : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (k + 1), monomial j ((k.choose j : ℚ) * ((m + k - j)! : ℚ))

private theorem coeff_reflectedContinuant (m k j : ℕ) :
    (reflectedContinuant m k).coeff j = (k.choose j : ℚ) * ((m + k - j)! : ℚ) := by
  by_cases hj : j ≤ k
  · simp [reflectedContinuant, coeff_monomial, Finset.mem_range, hj]
  · simp [reflectedContinuant, coeff_monomial, Finset.mem_range, hj,
      Nat.choose_eq_zero_of_lt (lt_of_not_ge hj)]

private theorem reflectedContinuant_zero (m : ℕ) :
    reflectedContinuant m 0 = C (m ! : ℚ) := by
  simp [reflectedContinuant, monomial_zero_left]

private theorem reflectedContinuant_one (m : ℕ) :
    reflectedContinuant m 1 = (X + C ((m : ℚ) + 1)) * C (m ! : ℚ) := by
  simp [reflectedContinuant, Finset.sum_range_succ, monomial_zero_left,
    ← C_mul_X_eq_monomial, Nat.factorial_succ, mul_add, mul_comm, add_comm]

private theorem reflectedContinuant_step (m k : ℕ) :
    reflectedContinuant m (k + 2) =
      (X + C ((m : ℚ) + k + 2)) * reflectedContinuant m (k + 1) -
        C ((k : ℚ) + 1) * (X * reflectedContinuant m k) := by
  ext j
  rw [add_mul, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul]
  cases j with
  | zero =>
    simp only [coeff_X_mul_zero, coeff_reflectedContinuant, Nat.choose_zero_right,
      Nat.cast_one, one_mul, Nat.sub_zero, zero_add, mul_zero, sub_zero]
    rw [show m + (k + 2) = (m + (k + 1)) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  | succ j =>
    simp only [coeff_X_mul, coeff_reflectedContinuant]
    rcases lt_trichotomy j (k + 1) with h | rfl | h
    · rw [Nat.choose_succ_succ', show m + (k + 2) - (j + 1) = m + (k + 1) - j by omega,
        show m + (k + 1) - (j + 1) = m + k - j by omega,
        show m + (k + 1) - j = (m + k - j) + 1 by omega, Nat.factorial_succ]
      have hchoose := Nat.add_one_mul_choose_eq k j
      have hchoose' : ((k : ℚ) + 1) * (k.choose j : ℚ) =
          ((k + 1).choose (j + 1) : ℚ) * ((j : ℚ) + 1) := by exact_mod_cast hchoose
      have hsub : ((m + k - j : ℕ) : ℚ) = (m : ℚ) + k - j := by
        rw [Nat.cast_sub (by omega), Nat.cast_add]
      push_cast
      rw [hsub]
      linear_combination ((m + k - j)! : ℚ) * hchoose'
    · rw [show k + 1 + 1 = k + 2 by omega]
      simp [show m + (k + 2) - (k + 2) = m by omega,
        show m + (k + 1) - (k + 1) = m by omega]
    · simp [Nat.choose_eq_zero_of_lt (show k + 2 < j + 1 by omega),
        Nat.choose_eq_zero_of_lt (show k + 1 < j + 1 by omega),
        Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (show k < j by omega)]

private theorem eval_reflectedContinuant_diagonal (m : ℕ) (z : ℂ) :
    aeval z (reflectedContinuant m m) = (((2 * m)! : ℕ) : ℂ) * aeval (-z) (denominator m) := by
  open D5.S3.Analytic.HalfIntegerBesselPolynomial in
  have hp : reflectedContinuant m m =
      C ((m ! : ℚ) * 2 ^ m) * (carrier m).reverse.comp (C (1 / 2) * X) := by
    ext j
    rw [coeff_reflectedContinuant, coeff_C_mul, comp_C_mul_X_coeff, coeff_reverse, natDegree_carrier]
    by_cases hj : j ≤ m
    · rw [revAt_le hj, coeff_carrier, coefficient, ite_eq_left (Nat.sub_le _ _),
        Nat.cast_choose ℚ hj, show m + (m - j) = 2 * m - j by omega,
        show m + m - j = 2 * m - j by omega, show m - (m - j) = j by omega]
      have hpow : (2 : ℚ) ^ (m - j) * 2 ^ j = 2 ^ m := by rw [← pow_add, Nat.sub_add_cancel hj]
      have hfact (k : ℕ) : (k ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      rw [div_pow, ← hpow]
      field_simp [hfact]
      rw [one_pow]
    · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hj), revAt_eq_self_of_lt (lt_of_not_ge hj),
        coeff_carrier, coefficient, ite_eq_right hj]
      simp
  have harg : aeval z (C (1 / 2 : ℚ) * X) = aeval (-z) (C (-1 / 2 : ℚ) * X) := by
    simp only [map_mul, aeval_C, aeval_X]
    change (((1 / 2 : ℚ) : ℂ) * z) = (((-1 / 2 : ℚ) : ℂ) * (-z))
    push_cast
    ring
  have hscale : (((2 * m)! : ℕ) : ℂ) * (normalization m : ℂ) = (m ! : ℂ) := by
    have hf : (((2 * m)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * m)
    push_cast [normalization]
    field_simp [hf]
  simp only [hp, denominator_eq_reverse, map_mul, aeval_C, aeval_comp, harg, map_natCast]
  change (m ! : ℂ) * _ * _ = (((2 * m)! : ℕ) : ℂ) * (((normalization m : ℂ) * _) * _)
  rw [← mul_assoc, ← mul_assoc, hscale]

private theorem parabolic_ratio {a : ℝ} (ha : 0 < a) {z u : ℂ}
    (hz : ‖z‖ - z.re < 2 * a) (hu : a ≤ u.re) :
    z + u ≠ 0 ∧ (z / (z + u)).re ≤ 1 := by
  have hnegre : -‖z‖ ≤ z.re := (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hzre : 0 < z.re + a := by linarith
  have hpos : 0 < (z + u).re := by rw [Complex.add_re]; linarith
  have hne : z + u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hpos; exact hpos.false
  refine ⟨hne, ?_⟩
  have hsq : z.im ^ 2 < 4 * a * (z.re + a) := by
    rw [← Complex.sq_norm_sub_sq_re]
    nlinarith [mul_pos (show 0 < z.re + 2 * a - ‖z‖ by linarith)
      (show 0 < z.re + 2 * a + ‖z‖ by linarith [norm_nonneg z])]
  have hprod := mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ u.re + a + z.re by linarith)
  rw [Complex.div_re, ← add_div, div_le_iff₀ (Complex.normSq_pos.mpr hne), one_mul,
    Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (u.im + z.im / 2)]

private theorem reflectedContinuant_ne_zero (m : ℕ) {z : ℂ}
    (hz : ‖z‖ - z.re < 2 * ((m : ℝ) + 1)) (k : ℕ) :
    aeval z (reflectedContinuant m k) ≠ 0 := by
  let P : ℕ → ℂ := fun k => aeval z (reflectedContinuant m k)
  have hα : 0 < (m : ℝ) + 1 := by positivity
  have hP0 : P 0 ≠ 0 := by
    simp [P, reflectedContinuant_zero, Nat.factorial_ne_zero]
  have hrec (k : ℕ) : P (k + 2) =
      (z + ((m : ℂ) + k + 2)) * P (k + 1) - ((k : ℂ) + 1) * (z * P k) := by
    simp [P, reflectedContinuant_step]
  have hchain : ∀ k, P k ≠ 0 ∧ ∃ u : ℂ, (m : ℝ) + 1 ≤ u.re ∧
      P (k + 1) = (z + u) * P k := by
    intro k
    induction k with
    | zero =>
      refine ⟨hP0, (m : ℂ) + 1, by simp, ?_⟩
      simp [P, reflectedContinuant_zero, reflectedContinuant_one]
    | succ k ih =>
      obtain ⟨hk, u, hu, hstep⟩ := ih
      obtain ⟨hzu, hratio⟩ := parabolic_ratio hα hz hu
      refine ⟨by rw [hstep]; exact mul_ne_zero hzu hk,
        (m : ℂ) + k + 2 - ((k : ℂ) + 1) * (z / (z + u)), ?_, ?_⟩
      · have hmul := mul_nonneg (show 0 ≤ (k : ℝ) + 1 by positivity)
          (sub_nonneg.mpr hratio)
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
        nlinarith
      · rw [hrec, hstep]
        field_simp
        ring
  exact (hchain k).1

/-- The parabolic exclusion for every root of the diagonal denominator. -/
theorem denominator_root_norm_add_re {m : ℕ} {ζ : ℂ}
    (hζ : aeval ζ (denominator m) = 0) : 2 * ((m : ℝ) + 1) ≤ ‖ζ‖ + ζ.re := by
  by_contra! h
  apply reflectedContinuant_ne_zero m (z := -ζ) (by simpa using h) m
  rw [eval_reflectedContinuant_diagonal, neg_neg, hζ, mul_zero]


private theorem re_eta_lt_at_equal_radius {w : ℂ} (hw : 0 < w.re) (him : w.im ≠ 0) :
    (eta w).re < (eta (‖w‖ : ℂ)).re := by
  let R := ‖w‖
  have hR : 0 < R := hw.trans_le (Complex.re_le_norm w)
  let arc (t : ℂ) := (R : ℂ) * Complex.exp (t * Complex.I)
  let f (t : ℝ) := (eta (arc t)).re
  have hre (t : ℝ) (ht : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
      0 < (arc t).re := by
    simpa [arc, Complex.mul_re, Complex.exp_ofReal_mul_I_re] using
      mul_pos hR (Real.cos_pos_of_mem_Ioo ht)
  have himage (t : ℝ) : (arc t).im = R * Real.sin t := by
    simp [arc, Complex.mul_im, Complex.exp_ofReal_mul_I_im]
  have hderiv (t : ℝ) (ht : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
      HasDerivAt f (-(S (arc t)).im) t := by
    have harc : HasDerivAt arc (arc t * Complex.I) (t : ℂ) :=
      (Complex.hasDerivAt_exp _ |>.comp (t : ℂ) ((hasDerivAt_id _).mul_const Complex.I)
        |>.const_mul (R : ℂ)).congr_deriv (by dsimp [arc]; ring)
    have hp := ((hasDerivAt_eta (hre t ht)).comp (t : ℂ) harc).comp_ofReal
    have hne : arc t ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne') (Complex.exp_ne_zero _)
    rw [show S (arc t) / arc t * (arc t * Complex.I) = S (arc t) * Complex.I by
      field_simp] at hp
    simpa [f, Function.comp_def, Complex.mul_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp
  have hsign (t : ℝ) (ht : t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
      (S (arc t)).re * (S (arc t)).im = (arc t).re * (R * Real.sin t) := by
    have hs := congrArg Complex.im (HalfIntegerBessel.S_sq (arc t))
    simp only [pow_two, Complex.mul_im, Complex.add_im, Complex.one_im, zero_add] at hs
    rw [himage] at hs
    linarith
  have hwa : arc (w.arg : ℂ) = w := Complex.norm_mul_exp_arg_mul_I w
  have ha : w.arg ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw))
  have hf0 : f 0 = (eta (R : ℂ)).re := by simp [f, arc]
  have hfa : f w.arg = (eta w).re := by rw [show f w.arg = (eta (arc w.arg)).re from rfl, hwa]
  rw [← hf0, ← hfa]
  have harg : w.arg ≠ 0 := fun h => by
    have hwim := congrArg Complex.im hwa
    simp [h, arc] at hwim
    exact him hwim.symm
  rcases lt_or_gt_of_ne harg with hneg | hpos
  · have hsub : Icc w.arg 0 ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      fun _ ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt Real.pi_div_two_pos⟩
    have hmono : StrictMonoOn f (Icc w.arg 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
        (fun t ht => (hderiv t (hsub ht)).continuousAt.continuousWithinAt)
      intro t ht
      rw [interior_Icc] at ht
      have ht' := hsub (Ioo_subset_Icc_self ht)
      rw [(hderiv t ht').deriv, neg_pos]
      have hs : Real.sin t < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt ht.2 (by linarith [ht'.1, Real.pi_pos])
      have hprod := mul_neg_of_pos_of_neg (hre t ht') (mul_neg_of_pos_of_neg hR hs)
      rw [← hsign t ht'] at hprod
      exact neg_of_mul_neg_right hprod (S_re_pos (hre t ht')).le
    exact hmono ⟨le_rfl, hneg.le⟩ ⟨hneg.le, le_rfl⟩ hneg
  · have hsub : Icc 0 w.arg ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      fun _ ht => ⟨(neg_lt_zero.mpr Real.pi_div_two_pos).trans_le ht.1, ht.2.trans_lt ha.2⟩
    have hanti : StrictAntiOn f (Icc 0 w.arg) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
        (fun t ht => (hderiv t (hsub ht)).continuousAt.continuousWithinAt)
      intro t ht
      rw [interior_Icc] at ht
      have ht' := hsub (Ioo_subset_Icc_self ht)
      rw [(hderiv t ht').deriv, neg_lt_zero]
      have hs : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht'.2, Real.pi_pos])
      have hprod := mul_pos (hre t ht') (mul_pos hR hs)
      rw [← hsign t ht'] at hprod
      exact pos_of_mul_pos_right hprod (S_re_pos (hre t ht')).le
    exact hanti ⟨le_rfl, hpos.le⟩ ⟨hpos.le, le_rfl⟩ hpos

private theorem re_eta_neg_of_norm_le {c : ℝ} (hc : 0 < c)
    (hzero : eta (c : ℂ) = 0) {w : ℂ} (hw : 0 < w.re) (hn : ‖w‖ ≤ c) (hne : w ≠ c) :
    (eta w).re < 0 := by
  have hmono : StrictMonoOn (fun x : ℝ => (eta (x : ℂ)).re) (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x hx => (etaReal_hasDerivAt hx).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ioi] at hx
    rw [(etaReal_hasDerivAt hx).deriv]
    exact div_pos (by positivity) hx
  have hnorm : 0 < ‖w‖ := hw.trans_le (Complex.re_le_norm w)
  have hle : (eta (‖w‖ : ℂ)).re ≤ (eta (c : ℂ)).re := hmono.monotoneOn hnorm hc hn
  have hlt : (eta w).re < (eta (c : ℂ)).re := by
    by_cases hi : w.im = 0
    · have he : (‖w‖ : ℂ) = w := by
        rw [Complex.norm_def, Complex.normSq_apply, hi, mul_zero, add_zero,
          ← sq, Real.sqrt_sq hw.le]
        exact Complex.ext rfl (by simpa using hi.symm)
      rw [← he]
      exact hmono hnorm hc (hn.lt_of_ne (fun h => hne (he.symm.trans (congrArg Complex.ofReal h))))
    · exact (re_eta_lt_at_equal_radius hw hi).trans_le hle
  simpa [hzero] using hlt


private theorem scaled_root_sector {m : ℕ} {w : ℂ}
    (hw : aeval (2 * (order m : ℂ) * w) (denominator m) = 0) :
    1 ≤ ‖w‖ + w.re := by
  have hν : 0 < order m := by unfold order; positivity
  have h := denominator_root_norm_add_re hw
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hν.le,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  have hbound : 2 * order m ≤ 2 * order m * (‖w‖ + w.re) := by
    unfold order at h ⊢
    norm_num at h
    linarith
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hbound) (by positivity)

private theorem exists_compact_exclusion {c ε : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hzero : eta (c : ℂ) = 0) (hε : 0 < ε) :
    ∃ d δ : ℝ, c < d ∧ d < 1 ∧ 0 < δ ∧ δ ≤ d - c ∧
      ∀ w : ℂ, ‖w‖ ≤ d → 1 ≤ ‖w‖ + w.re → ε ≤ ‖w - (c : ℂ)‖ →
        δ ≤ max (‖w‖ - c) |(eta w).re| := by
  let d := (1 + c) / 2
  have hcd : c < d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith
  let K : Set ℂ := closedBall 0 d ∩
    ({w | 1 ≤ ‖w‖ + w.re} ∩ {w | ε ≤ ‖w - (c : ℂ)‖})
  let f (w : ℂ) := max (‖w‖ - c) |(eta w).re|
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right <|
    (isClosed_le continuous_const (continuous_norm.add Complex.continuous_re)).inter
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  have hn (w : ℂ) (hw : w ∈ K) : ‖w‖ ≤ d := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw.1
  have hre (w : ℂ) (hw : w ∈ K) : 0 < w.re := by
    have hs : 1 ≤ ‖w‖ + w.re := hw.2.1
    linarith [hn w hw]
  have hη : ContinuousOn (fun w => (eta w).re) K := fun w hw =>
    Complex.continuous_re.continuousAt.comp
      (hasDerivAt_eta (hre w hw)).continuousAt |>.continuousWithinAt
  have hf : ContinuousOn f K :=
    (continuous_norm.sub continuous_const).continuousOn.sup hη.abs
  have hpositive (w : ℂ) (hw : w ∈ K) : 0 < f w := by
    by_cases h : ‖w‖ ≤ c
    · have hne : w ≠ (c : ℂ) := fun eq => by
        have hdist : ε ≤ ‖w - (c : ℂ)‖ := hw.2.2
        rw [eq, sub_self, norm_zero] at hdist
        exact hε.not_ge hdist
      have hphase := re_eta_neg_of_norm_le hc hzero (hre w hw) h hne
      exact (abs_pos.mpr hphase.ne).trans_le (le_max_right _ _)
    · exact (sub_pos.mpr (lt_of_not_ge h)).trans_le (le_max_left _ _)
  by_cases hne : K.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne hf
    refine ⟨d, min (d - c) (f w), hcd, hd1, lt_min (sub_pos.mpr hcd) (hpositive w hw),
      min_le_left _ _, ?_⟩
    intro v hv hs he
    have hvK : v ∈ K := ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hv, hs, he⟩
    exact (min_le_right _ _).trans (hmin hvK)
  · refine ⟨d, d - c, hcd, hd1, sub_pos.mpr hcd, le_rfl, ?_⟩
    intro w hw hs he
    exact (hne ⟨w, by simpa [Metric.mem_closedBall, dist_zero_right] using hw, hs, he⟩).elim

/-- At sufficiently large odd orders, every scaled pole outside a fixed neighborhood
of the positive phase zero has modulus uniformly larger than that zero. -/
theorem exists_uniform_scaled_exterior_radius {c ε : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hzero : eta (c : ℂ) = 0) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℕ, ∀ m ≥ M, Odd m → ∀ w : ℂ,
      aeval (2 * (order m : ℂ) * w) (denominator m) = 0 →
      w ∉ ball (c : ℂ) ε → c + δ ≤ ‖w‖ := by
  obtain ⟨d, δ, hcd, hd1, hδ, hδd, hcompact⟩ := exists_compact_exclusion hc hc1 hzero hε
  let κ := (1 - d) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hd : 0 < d := hc.trans hcd
  have hκ₁ : κ ≤ 1 := by dsimp [κ]; linarith
  let A := 15 * sectorMass κ / κ
  let T := 40 * sectorMass κ / κ
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (max T (A / δ)))
  refine ⟨δ, hδ, M, ?_⟩
  intro m hm hmOdd w hw hext
  by_cases hn : ‖w‖ ≤ d
  · have hsect := scaled_root_sector hw
    have hws : κ * ‖w‖ < w.re := by
      have hmul := mul_le_mul_of_nonneg_left hn hκ.le
      have hk := mul_le_of_le_one_right hκ.le hd1.le
      dsimp [κ] at *
      linarith
    have hνM : (M : ℝ) ≤ order m := by
      have hcast : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      unfold order
      linarith
    have hT : T ≤ order m := ((le_max_left T _).trans (le_max_right 1 _)).trans
      (hM.le.trans hνM)
    have hν : 1 ≤ order m := (le_max_left _ _).trans (hM.le.trans hνM)
    have hνsq : order m ≤ order m ^ 2 := by nlinarith
    have hsmall : A / order m ^ 2 < δ := by
      have hlt : A / δ < order m ^ 2 := calc
        _ ≤ max 1 (max T (A / δ)) := (le_max_right _ _).trans (le_max_right _ _)
        _ < (M : ℝ) := hM
        _ ≤ order m ^ 2 := hνM.trans hνsq
      rw [div_lt_iff₀ (by positivity)]
      simpa only [mul_comm (order m ^ 2)] using (div_lt_iff₀ hδ).mp hlt
    obtain ⟨j, hj⟩ := (denominator_zero_iff_polePhase m hmOdd hκ hκ₁ hT hws).mp hw
    have hreal : (polePhase m w).re = 0 := by
      rw [hj]
      simp [polePhaseLattice, Complex.div_re, Complex.mul_re]
    have hphase : |(eta w).re| < δ := calc
      _ = |(polePhase m w - eta w).re| := by rw [Complex.sub_re, hreal, zero_sub, abs_neg]
      _ ≤ ‖polePhase m w - eta w‖ := Complex.abs_re_le_norm _
      _ ≤ A / order m ^ 2 := (polePhase_sector m hκ hκ₁ hT hws).2.2.2.2
      _ < δ := hsmall
    have hdist : ε ≤ ‖w - (c : ℂ)‖ := by
      simpa [Metric.mem_ball, dist_eq_norm, not_lt] using hext
    have h := hcompact w hn hsect hdist
    rcases le_max_iff.mp h with h | h
    · linarith
    · exact (h.not_gt hphase).elim
  · linarith


/-- The distinct denominator roots outside the full lattice cutoff. -/
noncomputable def exteriorPoles (m : ℕ) (g : ℂ → ℂ) (t₀ : ℝ) : Finset ℂ := by
  classical
  exact ((denominator m).aroots ℂ).toFinset.filter fun ζ =>
    ∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ → ζ ≠ centralPole m g j

private theorem norm_sum_normalized_exterior_le (m n : ℕ) (hm : Odd m)
    {Λ r t₀ : ℝ} (hΛ : 0 < Λ) (hr : 0 < r)
    (hrroot : aeval (r : ℂ) (denominator m) = 0) {g : ℂ → ℂ}
    (hgap : ∀ ζ ∈ exteriorPoles m g t₀, Λ ≤ Real.log (‖ζ‖ / r))
    (hn : 1 / 4 ≤ (n : ℝ) / order m ^ 2) :
    ‖∑ ζ ∈ exteriorPoles m g t₀,
      (residueWeight m ζ / residueWeight m (r : ℂ)) * ((r : ℂ) / ζ) ^ n‖ ≤
      (m : ℝ) * Real.exp (-Λ * order m ^ 2 / 4) := by
  classical
  have hν : 0 < order m := by unfold order; positivity
  have hquarter : order m ^ 2 / 4 ≤ (n : ℝ) := by
    have h := (le_div_iff₀ (sq_pos_of_pos hν)).mp hn
    linarith
  have hcard : (exteriorPoles m g t₀).card ≤ m := by
    unfold exteriorPoles
    calc
      _ ≤ ((denominator m).aroots ℂ).toFinset.card := Finset.card_filter_le _ _
      _ ≤ ((denominator m).aroots ℂ).card := Multiset.toFinset_card_le _
      _ ≤ (denominator m).natDegree := card_roots_map_le_natDegree ..
      _ = m := natDegree_denominator m
  have hterm (ζ : ℂ) (hζ : ζ ∈ exteriorPoles m g t₀) :
      ‖(residueWeight m ζ / residueWeight m (r : ℂ)) * ((r : ℂ) / ζ) ^ n‖ ≤
        Real.exp (-Λ * order m ^ 2 / 4) := by
    have hmem := (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hζ).1)
    have hroot := (mem_aroots.mp hmem).2
    have hζne := (denominator_root_derivative m hroot).1
    have hz : 0 < ‖ζ‖ := norm_pos_iff.mpr hζne
    have hlog := hgap ζ hζ
    have hrz : r ≤ ‖ζ‖ := by
      have h := (Real.log_le_log_iff zero_lt_one (div_pos hz hr)).mp
        (by simpa using hΛ.le.trans hlog)
      simpa only [one_mul] using (le_div_iff₀ hr).mp h
    have hlog' : Real.log (r / ‖ζ‖) ≤ -Λ := by
      rw [Real.log_div hr.ne' hz.ne']
      rw [Real.log_div hz.ne' hr.ne'] at hlog
      linarith
    have hcast : (n : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ n + m + 1 by omega)
    calc
      _ ≤ (r / ‖ζ‖) ^ (n + m + 1) :=
        norm_normalized_residueWeight_le m n hm hr hrroot hroot hrz
      _ = Real.exp (((n + m + 1 : ℕ) : ℝ) * Real.log (r / ‖ζ‖)) := by
        rw [Real.exp_nat_mul, Real.exp_log (div_pos hr hz)]
      _ ≤ Real.exp (-Λ * order m ^ 2 / 4) := by
        apply Real.exp_le_exp.mpr
        have h₁ := mul_le_mul_of_nonneg_left hlog'
          (show 0 ≤ ((n + m + 1 : ℕ) : ℝ) by positivity)
        have h₂ := mul_le_mul_of_nonpos_right (hquarter.trans hcast) (neg_nonpos.mpr hΛ.le)
        linarith
  calc
    _ ≤ ∑ ζ ∈ exteriorPoles m g t₀,
        ‖(residueWeight m ζ / residueWeight m (r : ℂ)) * ((r : ℂ) / ζ) ^ n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ζ ∈ exteriorPoles m g t₀, Real.exp (-Λ * order m ^ 2 / 4) :=
      Finset.sum_le_sum hterm
    _ = ((exteriorPoles m g t₀).card : ℝ) * Real.exp (-Λ * order m ^ 2 / 4) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos _).le

private theorem exterior_log_gap {m : ℕ} {c δ ε t₀ r : ℝ} {g : ℂ → ℂ}
    (hc : 0 < c) (hδ : 0 < δ) (hgre : 0 < (g 0).re)
    (hrdef : r = 2 * order m * (g 0).re)
    (hgclose : ‖g 0 - (c : ℂ)‖ ≤ δ / 2)
    (hlocal : ∀ w ∈ ball (c : ℂ) ε, aeval (2 * (order m : ℂ) * w) (denominator m) = 0 ↔
      ∃ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ ∧ w = g (polePhaseLattice m j))
    (hexterior : ∀ w : ℂ, aeval (2 * (order m : ℂ) * w) (denominator m) = 0 →
      w ∉ ball (c : ℂ) ε → c + δ ≤ ‖w‖)
    (ζ : ℂ) (hζ : aeval ζ (denominator m) = 0)
    (hout : ∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ → ζ ≠ centralPole m g j) :
    Real.log ((c + δ) / (c + δ / 2)) ≤ Real.log (‖ζ‖ / r) := by
  have hν : 0 < order m := by unfold order; positivity
  let a : ℂ := 2 * (order m : ℂ)
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hν.ne')
  let w := ζ / a
  have hscale : a * w = ζ := mul_div_cancel₀ ζ ha
  have hwroot : aeval (2 * (order m : ℂ) * w) (denominator m) = 0 := by
    rwa [show 2 * (order m : ℂ) * w = ζ from hscale]
  have hwout : w ∉ ball (c : ℂ) ε := by
    intro hw
    obtain ⟨j, hj, he⟩ := (hlocal w hw).mp hwroot
    apply hout j hj
    rw [← hscale, he, centralPole]
  have hrad := hexterior w hwroot hwout
  have hcenter : (g 0).re ≤ c + δ / 2 := by
    have h := (Complex.re_le_norm (g 0 - (c : ℂ))).trans hgclose
    simpa only [Complex.sub_re, Complex.ofReal_re, sub_le_iff_le_add, add_comm c] using h
  have haNorm : ‖a‖ = 2 * order m := by simp [a, Real.norm_of_nonneg hν.le]
  have heq : ‖ζ‖ / r = ‖w‖ / (g 0).re := by
    rw [← hscale, norm_mul, haNorm]
    rw [hrdef]
    rw [mul_div_mul_left _ _ (by positivity)]
  rw [heq]
  apply Real.log_le_log (by positivity)
  exact div_le_div₀ (by positivity) hrad hgre hcenter

/-- The full central lattice leaves a uniform logarithmic gap at every exterior pole.
The sum of their normalized contributions is exponentially small in the diagonal window. -/
theorem exists_uniform_exterior_pole_gap {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hzero : eta (c : ℂ) = 0) :
    ∃ t₀ ε ρ Λ : ℝ, 0 < t₀ ∧ t₀ < ρ ∧ 0 < ε ∧ 0 < Λ ∧
      ∃ M : ℕ, ∀ m ≥ M, Odd m → ∃ (g : ℂ → ℂ) (r W : ℝ),
        0 < r ∧ 0 < W ∧ centralPole m g 0 = (r : ℂ) ∧
        residueWeight m (r : ℂ) = (W : ℂ) ∧
        AnalyticOnNhd ℂ g (ball 0 ρ) ∧
        (∀ s ∈ ball 0 ρ, polePhase m (g s) = s) ∧
        (∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ →
          aeval (centralPole m g j) (denominator m) = 0) ∧
        InjOn (centralPole m g) {j | ‖polePhaseLattice m j‖ ≤ t₀} ∧
        (∀ w ∈ ball (c : ℂ) ε, aeval (2 * (order m : ℂ) * w) (denominator m) = 0 ↔
          ∃ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ ∧ w = g (polePhaseLattice m j)) ∧
        (∀ ζ : ℂ, aeval ζ (denominator m) = 0 →
          (∀ j : ℤ, ‖polePhaseLattice m j‖ ≤ t₀ → ζ ≠ centralPole m g j) →
          Λ ≤ Real.log (‖ζ‖ / r)) ∧
        ∀ n : ℕ, (n : ℝ) / order m ^ 2 ∈ Icc (1 / 4) (1 / 2) →
          ‖∑ ζ ∈ exteriorPoles m g t₀,
            (residueWeight m ζ / residueWeight m (r : ℂ)) * ((r : ℂ) / ζ) ^ n‖ ≤
            (m : ℝ) * Real.exp (-Λ * order m ^ 2 / 4) := by
  obtain ⟨_, ε, ρ, B, t₀, _, hε, _, _, _, _, ht, htρ, _, _, M₁, hcentral⟩ :=
    exists_central_poles hc hzero
  obtain ⟨δ, hδ, M₂, hexterior⟩ := exists_uniform_scaled_exterior_radius hc hc1 hzero hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (B / (δ / 2)))
  let Λ := Real.log ((c + δ) / (c + δ / 2))
  have hΛ : 0 < Λ := Real.log_pos ((one_lt_div₀ (by positivity)).mpr (by linarith))
  refine ⟨t₀, ε, ρ, Λ, ht, htρ, hε, hΛ, max (max M₁ M₂) N, ?_⟩
  intro m hm hmOdd
  have hm₁ := ((le_max_left M₁ M₂).trans (le_max_left (max M₁ M₂) N)).trans hm
  have hm₂ := ((le_max_right M₁ M₂).trans (le_max_left (max M₁ M₂) N)).trans hm
  have hmN := (le_max_right (max M₁ M₂) N).trans hm
  obtain ⟨g, hgA, hginv, hgre, hgim, hgclose, hroots, hinj, _, _, hlocal⟩ :=
    hcentral m hm₁ hmOdd
  have hν : 0 < order m := by unfold order; positivity
  have hNν : (N : ℝ) ≤ order m := by
    have h : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmN
    unfold order
    linarith
  have hν₁ : 1 ≤ order m := (le_max_left _ _).trans (hN.le.trans hNν)
  have hδB : B / order m ^ 2 ≤ δ / 2 := by
    have hνsq : order m ≤ order m ^ 2 := by nlinarith
    have h := (le_max_right (1 : ℝ) _).trans (hN.le.trans (hNν.trans hνsq))
    rw [div_le_iff₀ (sq_pos_of_pos hν)]
    simpa only [mul_comm (order m ^ 2)] using (div_le_iff₀ (by positivity : 0 < δ / 2)).mp h
  let r := 2 * order m * (g 0).re
  have hr : 0 < r := by dsimp [r]; positivity
  have hg0 : ((g 0).re : ℂ) = g 0 := Complex.ext rfl (by simpa using hgim.symm)
  have hzeroPole : centralPole m g 0 = (r : ℂ) := by
    rw [centralPole, show polePhaseLattice m 0 = 0 by simp [polePhaseLattice]]
    simp only [r, Complex.ofReal_mul, Complex.ofReal_ofNat, hg0]
  have hrroot : aeval (r : ℂ) (denominator m) = 0 := by
    rw [← hzeroPole]
    exact hroots 0 (by simp [polePhaseLattice, ht.le])
  have hgap := exterior_log_gap hc hδ hgre (r := r) rfl (hgclose.trans hδB)
    hlocal (hexterior m hm₂ hmOdd)
  obtain ⟨W, hW, hweight⟩ := residueWeight_pos m hmOdd hr hrroot
  refine ⟨g, r, W, hr, hW, hzeroPole, hweight, hgA,
    fun s hs => (hginv s hs).2.1, hroots, hinj, hlocal, hgap, ?_⟩
  intro n hn
  apply norm_sum_normalized_exterior_le m n hmOdd hΛ hr hrroot _ hn.1
  intro ζ hζ
  classical
  have h := Finset.mem_filter.mp hζ
  exact hgap ζ (mem_aroots.mp (Multiset.mem_toFinset.mp h.1)).2 h.2

end D5.S3.Analytic.Polynomial.DiagonalPadeExterior
