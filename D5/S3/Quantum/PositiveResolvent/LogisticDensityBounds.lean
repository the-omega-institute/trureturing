/- GID: D5/S3/Quantum/PositiveResolvent/LogisticDensityBounds
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logistic density derivative identities, strict second-derivative bounds, and strict divided-difference density inequalities. -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

open scoped BigOperators Interval
open Set MeasureTheory intervalIntegral

namespace D5.S3.Quantum.PositiveResolvent

noncomputable def ell (r : ℝ) : ℝ := (r ^ 2 + Real.pi ^ 2) / (1 + Real.exp r)

noncomputable def jfun (r : ℝ) : ℝ := Real.exp (2 * r) * (r ^ 2 + Real.pi ^ 2) / (1 + Real.exp r) ^ 2

private lemma one_add_exp_ne_zero (r : ℝ) : 1 + Real.exp r ≠ 0 := by
  positivity

private lemma ell_hasDerivAt (r : ℝ) :
    HasDerivAt ell
      ((2 * r * (1 + Real.exp r) - (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
        (1 + Real.exp r) ^ 2) r := by
  unfold ell
  have hnum := (hasDerivAt_id r).pow 2 |>.add (hasDerivAt_const r (Real.pi ^ 2))
  have hden := (hasDerivAt_const r (1 : ℝ)).add (Real.hasDerivAt_exp r)
  have h := hnum.div hden (one_add_exp_ne_zero r)
  exact h.congr_deriv (by dsimp; field_simp; ring)

private lemma jfun_hasDerivAt (r : ℝ) :
    HasDerivAt jfun
      (Real.exp (2 * r) *
        ((2 * r + 2 * (r ^ 2 + Real.pi ^ 2)) * (1 + Real.exp r) -
          2 * (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
          (1 + Real.exp r) ^ 3) r := by
  unfold jfun
  have he := (Real.hasDerivAt_exp (2 * r)).comp r
      ((hasDerivAt_const r 2).mul (hasDerivAt_id r))
  have hp := (hasDerivAt_id r).pow 2 |>.add (hasDerivAt_const r (Real.pi ^ 2))
  have hd := ((hasDerivAt_const r (1 : ℝ)).add (Real.hasDerivAt_exp r)).pow 2
  have h := (he.mul hp).div hd (pow_ne_zero 2 (one_add_exp_ne_zero r))
  exact h.congr_deriv (by dsimp; field_simp; ring)

@[simp] theorem ell_deriv_formula (r : ℝ) :
    deriv ell r =
      (2 * r * (1 + Real.exp r) - (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
        (1 + Real.exp r) ^ 2 :=
  (ell_hasDerivAt r).deriv

@[simp] theorem jfun_deriv_formula (r : ℝ) :
    deriv jfun r =
      (Real.exp (2 * r) *
        ((2 * r + 2 * (r ^ 2 + Real.pi ^ 2)) * (1 + Real.exp r) -
          2 * (r ^ 2 + Real.pi ^ 2) * Real.exp r) /
          (1 + Real.exp r) ^ 3) :=
  (jfun_hasDerivAt r).deriv

private lemma jfun_gap_bracket_pos (r : ℝ) :
    0 < r ^ 2 + Real.pi ^ 2 - 3 * r - 5 * r * (Real.exp r)⁻¹ -
      2 * r * (Real.exp (2 * r))⁻¹ := by
  by_cases hr : r ≤ 0
  · have he : 0 < Real.exp r := Real.exp_pos r
    have he2 : 0 < Real.exp (2 * r) := Real.exp_pos (2 * r)
    have hp : 0 < r ^ 2 + Real.pi ^ 2 := by positivity
    have hri : 0 ≤ -3 * r := by linarith
    have h5 : 0 ≤ (-5 * r) * (Real.exp r)⁻¹ :=
      mul_nonneg (by nlinarith) (le_of_lt (inv_pos.mpr he))
    have h2 : 0 ≤ (-2 * r) * (Real.exp (2 * r))⁻¹ :=
      mul_nonneg (by nlinarith) (le_of_lt (inv_pos.mpr he2))
    nlinarith
  · have hr' : 0 ≤ r := le_of_not_ge hr
    have h1 : 0 < 1 + r := by linarith
    have h2 : 0 < 1 + 2 * r := by linarith
    have he : 0 < Real.exp r := Real.exp_pos r
    have he2 : 0 < Real.exp (2 * r) := Real.exp_pos (2 * r)
    have hE : 1 + r ≤ Real.exp r := by simpa [add_comm] using Real.add_one_le_exp r
    have hE2 : 1 + 2 * r ≤ Real.exp (2 * r) := by
      simpa [add_comm] using (Real.add_one_le_exp (2 * r))
    have hi : (Real.exp r)⁻¹ ≤ (1 + r)⁻¹ :=
      (inv_le_inv₀ he h1).2 hE
    have hi2 : (Real.exp (2 * r))⁻¹ ≤ (1 + 2 * r)⁻¹ :=
      (inv_le_inv₀ he2 h2).2 hE2
    have hfrac1 : 5 * r * (Real.exp r)⁻¹ ≤ 5 := by
      have hq : r / (1 + r) ≤ 1 := by
        apply (div_le_iff₀ h1).2
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hi hr'
      calc
        5 * r * (Real.exp r)⁻¹ = 5 * (r * (Real.exp r)⁻¹) := by ring
        _ ≤ 5 * (r * (1 + r)⁻¹) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 5 * (r / (1 + r)) := by rw [div_eq_mul_inv]
        _ ≤ 5 := by nlinarith [mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 5)]
    have hfrac2 : 2 * r * (Real.exp (2 * r))⁻¹ ≤ 1 := by
      have hq : (2 * r) / (1 + 2 * r) ≤ 1 := by
        apply (div_le_iff₀ h2).2
        nlinarith
      have hmul := mul_le_mul_of_nonneg_left hi2 hr'
      calc
        2 * r * (Real.exp (2 * r))⁻¹ = 2 * (r * (Real.exp (2 * r))⁻¹) := by ring
        _ ≤ 2 * (r * (1 + 2 * r)⁻¹) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * (r / (1 + 2 * r)) := by rw [div_eq_mul_inv]
        _ ≤ 1 := by simpa [div_eq_mul_inv, mul_assoc] using hq
    have hquad : 0 < r ^ 2 + Real.pi ^ 2 - 3 * r - 6 := by
      nlinarith [sq_nonneg (r - 3 / 2), Real.pi_gt_three]
    nlinarith

private lemma jfun_gap_formula (r : ℝ) :
    -2 * Real.exp r * deriv ell r - deriv jfun r =
      2 * (Real.exp r) ^ 3 / (1 + Real.exp r) ^ 3 *
        (r ^ 2 + Real.pi ^ 2 - 3 * r - 5 * r * (Real.exp r)⁻¹ -
          2 * r * (Real.exp (2 * r))⁻¹) := by
  rw [ell_deriv_formula, jfun_deriv_formula]
  have he : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have he2 : Real.exp (2 * r) ≠ 0 := (Real.exp_pos (2 * r)).ne'
  have hExp2 : Real.exp (2 * r) = (Real.exp r) ^ 2 := by
    rw [show 2 * r = r + r by ring, Real.exp_add]
    ring
  rw [hExp2]
  field_simp [he, he2]
  ring

theorem jfun_deriv_lt (r : ℝ) : deriv jfun r < -2 * Real.exp r * deriv ell r := by
  have hg := jfun_gap_formula r
  have hp : 0 < 2 * (Real.exp r) ^ 3 / (1 + Real.exp r) ^ 3 := by positivity
  have hb := jfun_gap_bracket_pos r
  have : 0 < -2 * Real.exp r * deriv ell r - deriv jfun r := by
    rw [hg]
    exact mul_pos hp hb
  linarith

private lemma ell_deriv_hasDerivAt (r : ℝ) :
    HasDerivAt (deriv ell)
      (2 / (1 + Real.exp r) + Real.exp r / (1 + Real.exp r) ^ 3 *
        ((r ^ 2 + Real.pi ^ 2) * (Real.exp r - 1) - 4 * r * (Real.exp r + 1))) r := by
  have hid := hasDerivAt_id r
  have he := Real.hasDerivAt_exp r
  have hd := (hasDerivAt_const r (1 : ℝ)).add he
  have hn := ((hid.const_mul 2).mul hd).sub
    (((hid.pow 2).add_const (Real.pi ^ 2)).mul he)
  have h := hn.div (hd.pow 2) (pow_ne_zero 2 (one_add_exp_ne_zero r))
  have hf : deriv ell = fun x =>
      (2 * x * (1 + Real.exp x) - (x ^ 2 + Real.pi ^ 2) * Real.exp x) /
        (1 + Real.exp x) ^ 2 := funext ell_deriv_formula
  rw [hf]
  exact h.congr_deriv (by dsimp; field_simp; ring)

private lemma ell_deriv2_formula (r : ℝ) :
    deriv (deriv ell) r =
      2 / (1 + Real.exp r) + Real.exp r / (1 + Real.exp r) ^ 3 *
        ((r ^ 2 + Real.pi ^ 2) * (Real.exp r - 1) - 4 * r * (Real.exp r + 1)) :=
  (ell_deriv_hasDerivAt r).deriv

private lemma nonneg_from_deriv {f g : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, 0 ≤ x → 0 ≤ g x)
    (h0 : f 0 = 0) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)).continuousOn
    · intro y hy; exact (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y).deriv]
      exact hg y (le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hy))
  have h := hm (by simp) hx hx
  simpa [h0] using h

private lemma sinh_cosh_gap_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ s * Real.cosh s - Real.sinh s := by
  exact sub_nonneg.mpr
    (D5.S3.Observer.Fluctuation.ThermalCoefficientFloor.sinh_le_self_mul_cosh_of_nonneg hs)

private lemma sinh_cosh_upper {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ (1 + s ^ 2 / 3) * Real.sinh s - s * Real.cosh s := by
  apply nonneg_from_deriv
    (g := fun x => x / 3 * (x * Real.cosh x - Real.sinh x)) _ _ (by simp) hs
  · intro x
    exact ((((hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).pow 2 |>.div_const 3)).mul (Real.hasDerivAt_sinh x)).sub
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x))).congr_deriv (by dsimp; ring)
  · intro x hx; exact mul_nonneg (by positivity) (sinh_cosh_gap_nonneg hx)

private lemma coth_bounds {r : ℝ} (hr : 0 < r) :
    2 * (Real.exp r - 1) ≤ r * (Real.exp r + 1) ∧
      r * (Real.exp r + 1) ≤ (2 + r ^ 2 / 6) * (Real.exp r - 1) := by
  have hl := sinh_cosh_gap_nonneg (show 0 ≤ r / 2 by linarith)
  have hu := sinh_cosh_upper (show 0 ≤ r / 2 by linarith)
  have he : 0 < Real.exp (r / 2) := Real.exp_pos _
  have heq : Real.exp (r / 2) * Real.exp (r / 2) = Real.exp r := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.sinh_eq, Real.cosh_eq, Real.exp_neg] at hl hu
  have hlm := mul_nonneg hl he.le
  have hum := mul_nonneg hu he.le
  field_simp at hlm hum
  rw [← pow_two] at heq
  rw [heq] at hlm hum
  constructor <;> nlinarith

private lemma ell_deriv2_bounds_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 < deriv (deriv ell) r ∧ deriv (deriv ell) r < 2 := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · subst r; rw [ell_deriv2_formula]; norm_num
  have he := Real.exp_pos r
  have hE : 0 < Real.exp r - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hpos)
  have hd : 0 < 1 + Real.exp r := by positivity
  have hc := coth_bounds hpos
  have hpi : 8 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hbr : 0 < (r ^ 2 + Real.pi ^ 2) * (Real.exp r - 1) -
      4 * r * (Real.exp r + 1) := by
    have hp := mul_pos (show 0 < r ^ 2 / 3 + Real.pi ^ 2 - 8 by nlinarith [sq_nonneg r]) hE
    nlinarith [hc.2]
  have hquad := Real.quadratic_le_exp_of_nonneg hr
  have hpilt : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hupper : (r ^ 2 + Real.pi ^ 2) * (Real.exp r - 1) -
      4 * r * (Real.exp r + 1) < 2 * (1 + Real.exp r) ^ 2 := by
    have hq : r ^ 2 + Real.pi ^ 2 < 14 + 2 * Real.exp r := by nlinarith
    have hqm := mul_lt_mul_of_pos_right hq hE
    nlinarith [hc.1]
  rw [ell_deriv2_formula]
  constructor
  · exact add_pos (div_pos (by norm_num) hd) (mul_pos (div_pos he (by positivity)) hbr)
  · have hm := mul_lt_mul_of_pos_left hupper (div_pos he (show 0 < (1 + Real.exp r)^3 by positivity))
    have heq : 2 / (1 + Real.exp r) +
        Real.exp r / (1 + Real.exp r)^3 * (2 * (1 + Real.exp r)^2) = 2 := by
      field_simp
    linarith

private lemma ell_deriv2_reflection (r : ℝ) :
    deriv (deriv ell) r + deriv (deriv ell) (-r) = 2 := by
  rw [ell_deriv2_formula, ell_deriv2_formula, Real.exp_neg]
  field_simp [Real.exp_ne_zero r]
  ring

theorem ell_deriv2_pos (r : ℝ) : 0 < deriv (deriv ell) r := by
  by_cases hr : 0 ≤ r
  · exact (ell_deriv2_bounds_nonneg hr).1
  · have h := (ell_deriv2_bounds_nonneg (show 0 ≤ -r by linarith)).2
    linarith [ell_deriv2_reflection r]

theorem density_bracket_pos_confluent (a : ℝ) :
    0 < 2 * (-deriv ell a) - Real.exp (-a) * deriv jfun a := by
  have h := mul_lt_mul_of_pos_left (jfun_deriv_lt a) (Real.exp_pos (-a))
  rw [Real.exp_neg] at h ⊢
  field_simp [Real.exp_ne_zero a] at h ⊢
  nlinarith

private lemma reverse_chebyshev {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hmf : Monotone f) (hmg : Antitone g) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * (∫ x in a..b, f x * g x) ≤
      (∫ x in a..b, f x) * (∫ x in a..b, g x) := by
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable a b
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have hfgi : IntervalIntegrable (fun x => f x * g x) volume a b :=
    (hf.mul hg).intervalIntegrable a b
  have hi (x : ℝ) :
      (∫ y in a..b, (f x - f y) * (g x - g y)) =
        (b - a) * (f x * g x) - f x * (∫ y in a..b, g y) -
          (∫ y in a..b, f y) * g x + (∫ y in a..b, f y * g y) := by
    have heq : (fun y => (f x - f y) * (g x - g y)) =
        fun y => ((f x * g x - f x * g y) - f y * g x) + f y * g y := by
      funext y; ring
    rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
      ring
    · exact intervalIntegrable_const
    · exact hgi.const_mul _
    · exact (intervalIntegrable_const.sub (hgi.const_mul _))
    · exact hfi.mul_const _
    · exact (intervalIntegrable_const.sub (hgi.const_mul _)).sub (hfi.mul_const _)
    · exact hfgi
  have hn (x : ℝ) :
      (b - a) * (f x * g x) - f x * (∫ y in a..b, g y) -
          (∫ y in a..b, f y) * g x + (∫ y in a..b, f y * g y) ≤ 0 := by
    rw [← hi x]
    have h := integral_mono_on (μ := volume)
      (f := fun y => (f x - f y) * (g x - g y)) hab
      (((continuous_const.sub hf).mul (continuous_const.sub hg)).intervalIntegrable a b)
      (intervalIntegrable_const (c := (0 : ℝ))) (fun y hy => ?_)
    · simpa using h
    · rcases le_total x y with hxy | hyx
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hmf hxy))
          (sub_nonneg.mpr (hmg hxy))
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hmf hyx))
          (sub_nonpos.mpr (hmg hyx))
  have ho := integral_mono_on (μ := volume) hab
    (((hfgi.const_mul _).sub (hfi.mul_const _)).sub (hgi.const_mul _)
      |>.add intervalIntegrable_const)
    (intervalIntegrable_const (c := (0 : ℝ))) (fun x hx => hn x)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_sub] at ho
  · simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const, intervalIntegral.integral_const, smul_eq_mul] at ho
    nlinarith
  · exact hfgi.const_mul _
  · exact hfi.mul_const _
  · exact (hfgi.const_mul _).sub (hfi.mul_const _)
  · exact hgi.const_mul _
  · exact ((hfgi.const_mul _).sub (hfi.mul_const _)).sub (hgi.const_mul _)
  · exact intervalIntegrable_const

private lemma continuous_ell_deriv : Continuous (deriv ell) :=
  continuous_iff_continuousAt.mpr (fun r => (ell_deriv_hasDerivAt r).continuousAt)

private lemma continuous_jfun_deriv : Continuous (deriv jfun) := by
  have heq := funext jfun_deriv_formula
  rw [heq]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro r; exact pow_ne_zero 3 (one_add_exp_ne_zero r)

theorem density_bracket_pos {a b : ℝ} (hab : a < b) :
    (jfun b - jfun a) / (Real.exp b - Real.exp a) <
      2 * (ell a - ell b) / (b - a) := by
  let w : ℝ → ℝ := fun r => -deriv ell r
  have hw : Continuous w := continuous_ell_deriv.neg
  have hwm : Antitone w := by
    apply antitone_of_deriv_nonpos
    · intro r; exact (ell_deriv_hasDerivAt r).differentiableAt.neg
    · intro r
      rw [show deriv w r = -deriv (deriv ell) r from
        (ell_deriv_hasDerivAt r).neg.deriv.trans (by rw [← (ell_deriv_hasDerivAt r).deriv])]
      exact neg_nonpos.mpr (ell_deriv2_pos r).le
  have hcheb := reverse_chebyshev Real.continuous_exp hw Real.exp_monotone hwm hab.le
  have hbound (r : ℝ) : deriv jfun r < 2 * (Real.exp r * w r) := by
    have h := mul_pos (Real.exp_pos r) (density_bracket_pos_confluent r)
    rw [Real.exp_neg] at h
    have heq : Real.exp r * (2 * (-deriv ell r) - (Real.exp r)⁻¹ * deriv jfun r) =
        2 * (Real.exp r * w r) - deriv jfun r := by
      dsimp [w]; field_simp
    rw [heq] at h
    linarith
  have hstrict : (∫ r in a..b, deriv jfun r) < ∫ r in a..b, 2 * (Real.exp r * w r) := by
    apply integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
      continuous_jfun_deriv.continuousOn ((Real.continuous_exp.mul hw).const_mul 2).continuousOn
    · intro r hr; exact (hbound r).le
    · refine ⟨a, ⟨le_rfl, hab.le⟩, ?_⟩
      exact hbound a
  have hj : (∫ r in a..b, deriv jfun r) = jfun b - jfun a :=
    integral_eq_sub_of_hasDerivAt (fun r hr => (jfun_hasDerivAt r).congr_deriv (jfun_deriv_formula r).symm)
      (continuous_jfun_deriv.intervalIntegrable a b)
  have he : (∫ r in a..b, Real.exp r) = Real.exp b - Real.exp a :=
    integral_eq_sub_of_hasDerivAt (fun r hr => Real.hasDerivAt_exp r)
      (Real.continuous_exp.intervalIntegrable a b)
  have hell : (∫ r in a..b, deriv ell r) = ell b - ell a :=
    integral_eq_sub_of_hasDerivAt (fun r hr => (ell_hasDerivAt r).congr_deriv (ell_deriv_formula r).symm)
      (continuous_ell_deriv.intervalIntegrable a b)
  have hwint : (∫ r in a..b, w r) = ell a - ell b := by
    change (∫ r in a..b, -deriv ell r) = _
    rw [intervalIntegral.integral_neg, hell]; ring
  rw [hj, intervalIntegral.integral_const_mul] at hstrict
  rw [he, hwint] at hcheb
  have hE : 0 < Real.exp b - Real.exp a := sub_pos.mpr (Real.exp_lt_exp.mpr hab)
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [div_lt_div_iff₀ hE hba]
  have hmul := mul_lt_mul_of_pos_right hstrict hba
  nlinarith

end D5.S3.Quantum.PositiveResolvent
