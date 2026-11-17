/- GID: D5/S3/Analytic/CanonicalProducts/TransversePoissonRemainder
   generality: G
   mirror-B: D5/B/S3/Analytic/CanonicalProducts/TransversePoissonRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrated logarithmic defects admit a signed uniform fourth-order Poisson remainder. -/

import D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! A signed fourth-order remainder for the integrated logarithmic defect. -/

open MeasureTheory
open scoped Topology BigOperators

noncomputable section
namespace D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
open D5.S3.Analytic.CanonicalProducts.IntegratedTransverseMoment

private lemma quadratic_pos {g : ℝ} (hg : 0 < g) (x : ℝ) :
    0 < x^2 + g^2 := by
  nlinarith [sq_nonneg x, sq_pos_of_pos hg]

private lemma log_ratio_continuous {g : ℝ} (hg : 0 < g) (T : ℝ) :
    Continuous (fun v : ℝ =>
      Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2))) := by
  exact ((((continuous_const.add continuous_id).pow 2).add continuous_const).div
    (((continuous_const.sub continuous_id).pow 2).add continuous_const)
    (fun v => (quadratic_pos hg (T - v)).ne')).log
      (fun v => (div_pos (quadratic_pos hg (T + v))
        (quadratic_pos hg (T - v))).ne')

private lemma log_ratio_hasDerivAt {g : ℝ} (hg : 0 < g) (T v : ℝ) :
    HasDerivAt (fun x : ℝ =>
      Real.log (((T + x)^2 + g^2) / ((T - x)^2 + g^2)))
      (4 * T * (T^2 + g^2 - v^2) /
        (((T + v)^2 + g^2) * ((T - v)^2 + g^2))) v := by
  have hfun : (fun x : ℝ =>
      Real.log (((T + x)^2 + g^2) / ((T - x)^2 + g^2))) =
      (fun x : ℝ => Real.log ((T + x)^2 + g^2) -
        Real.log ((T - x)^2 + g^2)) := by
    funext x
    exact Real.log_div (quadratic_pos hg (T + x)).ne'
      (quadratic_pos hg (T - x)).ne'
  rw [hfun]
  have hp := ((((hasDerivAt_const v T).add (hasDerivAt_id v)).pow 2).add_const
    (g^2)).log (quadratic_pos hg (T + v)).ne'
  have hm := ((((hasDerivAt_const v T).sub (hasDerivAt_id v)).pow 2).add_const
    (g^2)).log (quadratic_pos hg (T - v)).ne'
  convert hp.sub hm using 1
  · rfl
  · norm_num
    field_simp [(quadratic_pos hg (T + v)).ne',
      (quadratic_pos hg (T - v)).ne']
    <;> ring

private lemma rational_remainder_bounds {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 4) :
    1 - 3 * r ≤ (1 - r) / (1 + r)^2 ∧
    1 / (1 - r) ≤ 1 + (4 / 3 : ℝ) * r := by
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hp)).2
    nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 5 + 3 * r by linarith)]
  · apply (div_le_iff₀ hm).2
    nlinarith [mul_nonneg hr0 (show 0 ≤ 1 - 4 * r by linarith)]

-- This is the new scalar estimate. The two denominator identities preserve A⁻².
private lemma derivative_remainder_bounds {v g T : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) (hg : 0 < g) (hT : 1 ≤ T) :
    -12 * T * v^2 / (T^2 + g^2)^2 ≤
      4 * T * (T^2 + g^2 - v^2) /
        (((T + v)^2 + g^2) * ((T - v)^2 + g^2)) -
          4 * T / (T^2 + g^2) ∧
    4 * T * (T^2 + g^2 - v^2) /
        (((T + v)^2 + g^2) * ((T - v)^2 + g^2)) -
          4 * T / (T^2 + g^2) ≤
      16 * T * v^2 / (3 * (T^2 + g^2)^2) := by
  let A : ℝ := T^2 + g^2
  let D : ℝ := ((T + v)^2 + g^2) * ((T - v)^2 + g^2)
  let r : ℝ := v^2 / A
  have hT0 : 0 ≤ T := by linarith
  have hA : 0 < A := quadratic_pos hg T
  have hA1 : 1 ≤ A := by
    dsimp [A]
    nlinarith only [hT, sq_nonneg g, sq_nonneg (T - 1)]
  have hv2 : v^2 ≤ 1 / 4 := by
    nlinarith only [hv1, mul_nonneg hv0 (sub_nonneg.mpr hv1)]
  have hminus : 0 < A - v^2 := by linarith
  have hplus : 0 < A + v^2 := by positivity
  have hD : 0 < D := mul_pos (quadratic_pos hg (T + v))
    (quadratic_pos hg (T - v))
  have hDminus : D = (A - v^2)^2 + 4 * g^2 * v^2 := by
    dsimp [A, D]
    ring
  have hDplus : D = (A + v^2)^2 - 4 * T^2 * v^2 := by
    dsimp [A, D]
    ring
  have hDlower : (A - v^2)^2 ≤ D := by
    rw [hDminus]
    exact le_add_of_nonneg_right (by positivity)
  have hDupper : D ≤ (A + v^2)^2 := by
    rw [hDplus]
    exact sub_le_self _ (by positivity)
  have hr0 : 0 ≤ r := div_nonneg (sq_nonneg v) hA.le
  have hr1 : r ≤ 1 / 4 := by
    apply (div_le_iff₀ hA).2
    linarith
  have hrminus : 0 < 1 - r := by linarith
  have hrplus : 0 < 1 + r := by linarith
  have hnormlower : (1 - r) / (1 + r)^2 ≤ A * (A - v^2) / D := by
    calc
      _ = A * (A - v^2) / (A + v^2)^2 := by
        dsimp [r]
        field_simp [hA.ne', hplus.ne', hrplus.ne'] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hA.le hminus.le)
        hD hDupper
  have hnormupper : A * (A - v^2) / D ≤ 1 / (1 - r) := by
    calc
      _ ≤ A * (A - v^2) / (A - v^2)^2 :=
        div_le_div_of_nonneg_left (mul_nonneg hA.le hminus.le)
          (sq_pos_of_pos hminus) hDlower
      _ = _ := by
        dsimp [r]
        field_simp [hA.ne', hminus.ne', hrminus.ne'] <;> ring
  have hrational := rational_remainder_bounds hr0 hr1
  have hscaledlower := hrational.1.trans hnormlower
  have hscaledupper := hnormupper.trans hrational.2
  have hc : 0 ≤ 4 * T / A := div_nonneg (by positivity) hA.le
  change -12 * T * v^2 / A^2 ≤ 4 * T * (A - v^2) / D - 4 * T / A ∧
    4 * T * (A - v^2) / D - 4 * T / A ≤ 16 * T * v^2 / (3 * A^2)
  constructor
  · calc
      _ = (4 * T / A) * (1 - 3 * r) - 4 * T / A := by
        dsimp [r]
        field_simp [hA.ne'] <;> ring
      _ ≤ (4 * T / A) * (A * (A - v^2) / D) - 4 * T / A :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hscaledlower hc) _
      _ = _ := by field_simp [hA.ne', hD.ne'] <;> ring
  · calc
      _ = (4 * T / A) * (A * (A - v^2) / D) - 4 * T / A := by
        field_simp [hA.ne', hD.ne'] <;> ring
      _ ≤ (4 * T / A) * (1 + (4 / 3 : ℝ) * r) - 4 * T / A :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hscaledupper hc) _
      _ = _ := by
        dsimp [r]
        field_simp [hA.ne'] <;> ring

-- First FTC integration: derivative remainder to cubic logarithmic remainder.
private lemma log_ratio_remainder_bounds {v g T : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) (hg : 0 < g) (hT : 1 ≤ T) :
    -4 * T * v^3 / (T^2 + g^2)^2 ≤
      Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) -
        4 * T * v / (T^2 + g^2) ∧
    Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2)) -
        4 * T * v / (T^2 + g^2) ≤
      16 * T * v^3 / (9 * (T^2 + g^2)^2) := by
  let A : ℝ := T^2 + g^2
  let f : ℝ → ℝ := fun x =>
    Real.log (((T + x)^2 + g^2) / ((T - x)^2 + g^2))
  let d : ℝ → ℝ := fun x =>
    4 * T * (A - x^2) / (((T + x)^2 + g^2) * ((T - x)^2 + g^2)) -
      4 * T / A
  have hd (x : ℝ) : HasDerivAt (fun x => f x - (4 * T / A) * x) (d x) x := by
    convert (log_ratio_hasDerivAt hg T x).sub
      ((hasDerivAt_id x).const_mul (4 * T / A)) using 1 <;> first | rfl | (dsimp [f, d, A]; ring)
  have hnum : Continuous (fun x : ℝ => 4 * T * (A - x^2)) :=
    continuous_const.mul (continuous_const.sub (continuous_id.pow 2))
  have hden : Continuous (fun x : ℝ =>
      ((T + x)^2 + g^2) * ((T - x)^2 + g^2)) :=
    (((continuous_const.add continuous_id).pow 2).add continuous_const).mul
      (((continuous_const.sub continuous_id).pow 2).add continuous_const)
  have hdc : Continuous d :=
    (hnum.div hden (fun x => (mul_pos (quadratic_pos hg (T + x))
      (quadratic_pos hg (T - x))).ne')).sub continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hdc.intervalIntegrable (μ := volume) 0 v)
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [add_zero, sub_zero, div_self (quadratic_pos hg T).ne', Real.log_one]
  rw [hf0, mul_zero, sub_zero, sub_zero] at hFTC
  have hlow : IntervalIntegrable (fun x : ℝ => (-12 * T / A^2) * x^2)
      volume 0 v :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable (μ := volume) 0 v
  have hhigh : IntervalIntegrable (fun x : ℝ => (16 * T / (3 * A^2)) * x^2)
      volume 0 v :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable (μ := volume) 0 v
  have hL : (∫ x in (0 : ℝ)..v, (-12 * T / A^2) * x^2) ≤
      ∫ x in (0 : ℝ)..v, d x := by
    apply intervalIntegral.integral_mono_on hv0 hlow
      (hdc.intervalIntegrable (μ := volume) 0 v)
    intro x hx
    have hb := (derivative_remainder_bounds hx.1 (hx.2.trans hv1) hg hT).1
    convert hb using 1 <;> dsimp [d, A] <;> ring
  have hU : (∫ x in (0 : ℝ)..v, d x) ≤
      ∫ x in (0 : ℝ)..v, (16 * T / (3 * A^2)) * x^2 := by
    apply intervalIntegral.integral_mono_on hv0
      (hdc.intervalIntegrable (μ := volume) 0 v) hhigh
    intro x hx
    have hb := (derivative_remainder_bounds hx.1 (hx.2.trans hv1) hg hT).2
    convert hb using 1 <;> dsimp [d, A] <;> ring
  rw [hFTC, intervalIntegral.integral_const_mul, integral_pow] at hL hU
  norm_num only [Nat.reduceAdd, zero_pow, sub_zero, Nat.cast_ofNat] at hL hU
  constructor
  · convert hL using 1 <;> dsimp [f, A] <;> ring
  · convert hU using 1 <;> dsimp [f, A] <;>
      field_simp [(quadratic_pos hg T).ne'] <;> ring

-- Second integration: the error has the full T*a⁴/(T²+g²)² scale.
private lemma endpoint_remainder_bounds {a g T : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (hg : 0 < g) (hT : 1 ≤ T) :
    -(a^4 * T / (T^2 + g^2)^2) ≤
      endpointKernel a g T - 2 * (a^2 * T / (T^2 + g^2)) ∧
    endpointKernel a g T - 2 * (a^2 * T / (T^2 + g^2)) ≤
      (4 / 9 : ℝ) * (a^4 * T / (T^2 + g^2)^2) := by
  let A : ℝ := T^2 + g^2
  let f : ℝ → ℝ := fun v =>
    Real.log (((T + v)^2 + g^2) / ((T - v)^2 + g^2))
  have hf : Continuous f := log_ratio_continuous hg T
  have hlinear : Continuous (fun v : ℝ => (4 * T / A) * v) :=
    continuous_const.mul continuous_id
  have herror : Continuous (fun v : ℝ => f v - (4 * T / A) * v) := hf.sub hlinear
  have hlow : IntervalIntegrable (fun v : ℝ => (-4 * T / A^2) * v^3)
      volume 0 a :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable (μ := volume) 0 a
  have hhigh : IntervalIntegrable (fun v : ℝ => (16 * T / (9 * A^2)) * v^3)
      volume 0 a :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable (μ := volume) 0 a
  have hL : (∫ v in (0 : ℝ)..a, (-4 * T / A^2) * v^3) ≤
      ∫ v in (0 : ℝ)..a, f v - (4 * T / A) * v := by
    apply intervalIntegral.integral_mono_on ha0 hlow
      (herror.intervalIntegrable (μ := volume) 0 a)
    intro v hv
    have hb := (log_ratio_remainder_bounds hv.1 (hv.2.trans ha1) hg hT).1
    convert hb using 1 <;> dsimp [f, A] <;> ring
  have hU : (∫ v in (0 : ℝ)..a, f v - (4 * T / A) * v) ≤
      ∫ v in (0 : ℝ)..a, (16 * T / (9 * A^2)) * v^3 := by
    apply intervalIntegral.integral_mono_on ha0
      (herror.intervalIntegrable (μ := volume) 0 a) hhigh
    intro v hv
    have hb := (log_ratio_remainder_bounds hv.1 (hv.2.trans ha1) hg hT).2
    convert hb using 1 <;> dsimp [f, A] <;> ring
  have heq : (∫ v in (0 : ℝ)..a, f v - (4 * T / A) * v) =
      endpointKernel a g T - 2 * (a^2 * T / A) := by
    rw [intervalIntegral.integral_sub
      (hf.intervalIntegrable (μ := volume) 0 a)
      (hlinear.intervalIntegrable (μ := volume) 0 a),
      intervalIntegral.integral_const_mul, integral_id]
    change endpointKernel a g T - (4 * T / A) * ((a^2 - 0^2) / 2) = _
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_pow] at hL hU
  norm_num only [Nat.reduceAdd, zero_pow, sub_zero, Nat.cast_ofNat] at hL hU
  constructor
  · convert hL using 1 <;> dsimp [A] <;> ring
  · convert hU using 1 <;> dsimp [A] <;>
      field_simp [(quadratic_pos hg T).ne'] <;> ring

theorem integrated_defect_poisson_remainder {I : Type*} (w a gamma : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1 / 2)
    (hgamma : ∀ i, 0 < gamma i)
    (hbudget : Summable (fun i => w i * (a i)^2 / (gamma i)^2))
    (T : ℝ) (hT : 1 ≤ T) :
    Summable (fun i => w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ∧
    -(∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ≤
      integratedDefect w a gamma T -
        2 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) ∧
    integratedDefect w a gamma T -
        2 * (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) ≤
      (4 / 9 : ℝ) * (∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ∧
    (∑' i, w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2) ≤
      (∑' i, w i * (a i)^2 * T / (T^2 + (gamma i)^2)) / (4 * T^2) := by
  classical
  have hTpos : 0 < T := by linarith
  have hT0 : 0 ≤ T := hTpos.le
  have hT2 : 0 < T^2 := sq_pos_of_pos hTpos
  let q : I → ℝ := fun i => w i * (a i)^2 * T / (T^2 + (gamma i)^2)
  let rho : I → ℝ := fun i => w i * (a i)^4 * T / (T^2 + (gamma i)^2)^2
  let e : I → ℝ := fun i => w i * endpointKernel (a i) (gamma i) T
  let d : I → ℝ := fun i => e i - 2 * q i
  have hq0 (i : I) : 0 ≤ q i := by
    exact div_nonneg (mul_nonneg (mul_nonneg (hw i) (sq_nonneg _)) hT0)
      (quadratic_pos (hgamma i) T).le
  have hqbudget (i : I) : q i ≤ T * (w i * (a i)^2 / (gamma i)^2) := by
    calc
      q i ≤ w i * (a i)^2 * T / (gamma i)^2 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (hw i) (sq_nonneg _)) hT0)
          (sq_pos_of_pos (hgamma i)) (by nlinarith [sq_nonneg T])
      _ = _ := by ring
  have hq : Summable q := Summable.of_nonneg_of_le hq0 hqbudget (hbudget.mul_left T)
  have hrho0 (i : I) : 0 ≤ rho i := by
    exact div_nonneg (mul_nonneg (mul_nonneg (hw i) (pow_nonneg (ha0 i) 4)) hT0)
      (sq_nonneg _)
  have hrhoq (i : I) : rho i ≤ q i / (4 * T^2) := by
    have hA := quadratic_pos (hgamma i) T
    have ha2 : (a i)^2 ≤ 1 / 4 := by
      nlinarith only [ha1 i, mul_nonneg (ha0 i) (sub_nonneg.mpr (ha1 i))]
    have hfrac : (a i)^2 / (T^2 + (gamma i)^2) ≤ 1 / (4 * T^2) := by
      apply (div_le_div_iff₀ hA (mul_pos (by norm_num : (0 : ℝ) < 4) hT2)).2
      nlinarith [mul_le_mul_of_nonneg_right ha2 hT2.le, sq_nonneg (gamma i)]
    calc
      rho i = q i * ((a i)^2 / (T^2 + (gamma i)^2)) := by
        dsimp [rho, q]
        field_simp [hA.ne'] <;> ring
      _ ≤ q i * (1 / (4 * T^2)) := mul_le_mul_of_nonneg_left hfrac (hq0 i)
      _ = _ := by ring
  have hrho : Summable rho :=
    Summable.of_nonneg_of_le hrho0 hrhoq (hq.div_const (4 * T^2))
  have hd_bounds (i : I) : -rho i ≤ d i ∧ d i ≤ (4 / 9 : ℝ) * rho i := by
    have hs := endpoint_remainder_bounds (ha0 i) (ha1 i) (hgamma i) hT
    constructor
    · have hb := mul_le_mul_of_nonneg_left hs.1 (hw i)
      convert hb using 1 <;> dsimp [rho, d, e, q] <;> ring
    · have hb := mul_le_mul_of_nonneg_left hs.2 (hw i)
      convert hb using 1 <;> dsimp [rho, d, e, q] <;> ring
  have hdabs (i : I) : |d i| ≤ rho i := by
    apply abs_le.mpr
    constructor
    · exact (hd_bounds i).1
    · exact (hd_bounds i).2.trans (by nlinarith [hrho0 i])
  have hd : Summable d := hrho.of_norm_bounded (fun i => by
    simpa only [Real.norm_eq_abs] using hdabs i)
  have he : Summable e := by
    convert (hq.mul_left 2).add hd using 1
    ext i
    dsimp [d]
    ring
  have hidentity : integratedDefect w a gamma T = ∑' i, e i :=
    (integrated_transverse_moment w a gamma hw ha0 ha1 hgamma hbudget).2.2.2.2.1 T hT0
  have herror : integratedDefect w a gamma T - 2 * (∑' i, q i) = ∑' i, d i := by
    rw [hidentity]
    exact (he.hasSum.sub (hq.hasSum.mul_left 2)).tsum_eq.symm
  have hsumlower : -(∑' i, rho i) ≤ ∑' i, d i := by
    calc
      _ = ∑' i, -rho i := hrho.hasSum.neg.tsum_eq.symm
      _ ≤ _ := Summable.tsum_le_tsum (fun i => (hd_bounds i).1) hrho.neg hd
  have hsumupper : (∑' i, d i) ≤ (4 / 9 : ℝ) * (∑' i, rho i) := by
    calc
      _ ≤ ∑' i, (4 / 9 : ℝ) * rho i :=
        Summable.tsum_le_tsum (fun i => (hd_bounds i).2) hd (hrho.mul_left (4 / 9 : ℝ))
      _ = _ := hrho.tsum_mul_left (4 / 9 : ℝ)
  have hsumrho : (∑' i, rho i) ≤ (∑' i, q i) / (4 * T^2) := by
    calc
      _ ≤ ∑' i, q i / (4 * T^2) :=
        Summable.tsum_le_tsum hrhoq hrho (hq.div_const (4 * T^2))
      _ = _ := tsum_div_const
  change Summable rho ∧
    -(∑' i, rho i) ≤ integratedDefect w a gamma T - 2 * (∑' i, q i) ∧
    integratedDefect w a gamma T - 2 * (∑' i, q i) ≤
      (4 / 9 : ℝ) * (∑' i, rho i) ∧
    (∑' i, rho i) ≤ (∑' i, q i) / (4 * T^2)
  refine ⟨hrho, ?_, ?_, hsumrho⟩
  · rw [herror]
    exact hsumlower
  · rw [herror]
    exact hsumupper

end D5.S3.Analytic.CanonicalProducts.TransversePoissonRemainder
