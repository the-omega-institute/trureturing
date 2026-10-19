/- GID: D5/S3/Arith/Robin/OriginalEarlyDivisorQuadrature
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/OriginalEarlyDivisorQuadrature
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The literal early divisor quadrature retains its signed initial endpoint. -/

import D5.S3.Arith.Robin.OriginalMovingWindowMoment
import D5.S3.Weil.ZetaPntBase.EulerMaclaurin
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter Finset
open scoped Topology
open D5.S3.Arith.Robin.OriginalMovingWindowMoment (kernel endpoint width)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (g)
open D5.S3.Arith.Robin.MellinWeightedVariation (weight)

namespace D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature

/-- The literal Bernoulli endpoint, including value -1/2 at integers. -/
def betaOne (y : ℝ) : ℝ := Int.fract y - 1 / 2

private def bernoulliPrimitive (y : ℝ) : ℝ :=
  (Int.fract y ^ 2 - Int.fract y + 1 / 6) / 2

private lemma primitive_continuous : Continuous bernoulliPrimitive := by
  have hc : ContinuousOn (fun y : ℝ => (y ^ 2 - y + 1 / 6) / 2) (Icc 0 1) := by
    fun_prop
  exact hc.comp_fract'' (by norm_num)

private lemma primitive_bound (y : ℝ) : |bernoulliPrimitive y| ≤ 1 / 12 := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  have hs := sq_nonneg (Int.fract y - 1 / 2)
  have hp := mul_nonneg h0 (sub_nonneg.mpr h1.le)
  unfold bernoulliPrimitive
  apply abs_le.mpr
  constructor <;> nlinarith

private lemma primitive_right_deriv (y : ℝ) :
    HasDerivWithinAt bernoulliPrimitive (betaOne y) (Ioi y) y := by
  have he : ∀ᶠ x in 𝓝[≥] y, Int.floor x = Int.floor y :=
    tendsto_pure.mp (tendsto_floor_right_pure_floor y)
  have he' : ∀ᶠ x in 𝓝[>] y, Int.floor x = Int.floor y :=
    he.filter_mono (nhdsWithin_mono y Ioi_subset_Ici_self)
  let p : ℝ → ℝ := fun x => ((x - (Int.floor y : ℝ)) ^ 2 -
    (x - (Int.floor y : ℝ)) + 1 / 6) / 2
  have hd : HasDerivAt p (betaOne y) y := by
    have h := (((hasDerivAt_id y).sub_const (Int.floor y : ℝ)).pow 2).sub
      ((hasDerivAt_id y).sub_const (Int.floor y : ℝ))
    convert (h.add_const (1 / 6 : ℝ)).div_const 2 using 1 <;>
      first | rfl | (simp only [p, betaOne, Int.fract, id_eq, Nat.reduceSub, pow_one, mul_one]; ring)
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [he'] with x hx
    simp only [bernoulliPrimitive, Int.fract, p, hx]
  · rfl

private lemma beta_eq_B1 {y : ℝ} (hy : 0 ≤ y) : betaOne y = B1 y := by
  simp only [betaOne, B1, Int.fract, natCast_floor_eq_intCast_floor hy]

private lemma beta_integrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable betaOne volume a b := by
  rw [intervalIntegrable_iff']
  apply Measure.integrableOn_of_bounded (by simp) (by
    unfold betaOne
    fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [uIcc_of_le hab] at hx
  rw [Real.norm_eq_abs, beta_eq_B1 (ha.trans hx.1)]
  exact abs_B1_le_half (ha.trans hx.1)

/-- The same periodic primitive, centered at the midpoint of its range. -/
def centeredPrimitive (y : ℝ) : ℝ := bernoulliPrimitive y - 1 / 48

private lemma centered_primitive_bound (y : ℝ) : |centeredPrimitive y| ≤ 1 / 16 := by
  have h0 := Int.fract_nonneg y
  have h1 := Int.fract_lt_one y
  have hs := sq_nonneg (Int.fract y - 1 / 2)
  have hp := mul_nonneg h0 (sub_nonneg.mpr h1.le)
  unfold centeredPrimitive bernoulliPrimitive
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

private lemma primitive_parts {a b : ℝ} {v v' : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hc : ContinuousOn v' (Icc a b)) (c : ℝ) :
    (∫ x in a..b, v x * betaOne x) =
      v b * (bernoulliPrimitive b - c) - v a * (bernoulliPrimitive a - c) -
        ∫ x in a..b, v' x * (bernoulliPrimitive x - c) := by
  have hvc : ContinuousOn v (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun x hx => (hv x hx).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hvc (primitive_continuous.sub continuous_const).continuousOn
    (fun x hx => (hv x (by rw [min_eq_left hab, max_eq_right hab] at hx; exact ⟨hx.1.le, hx.2.le⟩)).hasDerivWithinAt)
    (fun x _ => (primitive_right_deriv x).sub_const c)
    ((uIcc_of_le hab ▸ hc).intervalIntegrable) (beta_integrable ha hab)

/-- The centered bound is consumed by the old estimate and by actual density cells. -/
private lemma centered_negative_bound {a b : ℝ} {v v' : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hc : ContinuousOn v' (Icc a b))
    (hn : ∀ x ∈ Icc a b, v x ≤ 0)
    (hp : ∀ x ∈ Icc a b, 0 ≤ v' x) :
    |∫ x in a..b, v x * betaOne x| ≤ -v a / 8 := by
  have hvic : IntervalIntegrable v' volume a b :=
    (uIcc_of_le hab ▸ hc).intervalIntegrable
  have hft : (∫ x in a..b, v' x) = v b - v a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hv x (uIcc_of_le hab ▸ hx)) hvic
  have hi : |∫ x in a..b, v' x * centeredPrimitive x| ≤ (v b - v a) / 16 := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ∫ x in a..b, v' x / 16 := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · filter_upwards [] with x hx
          have hpx := hp x ⟨hx.1.le, hx.2⟩
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpx]
          exact (mul_le_mul_of_nonneg_left (centered_primitive_bound x) hpx).trans_eq (by ring)
        · exact hvic.div_const 16
      _ = _ := by rw [intervalIntegral.integral_div, hft]
  have he := primitive_parts ha hab hv hc (1 / 48)
  change (∫ x in a..b, v x * betaOne x) =
    v b * centeredPrimitive b - v a * centeredPrimitive a -
      ∫ x in a..b, v' x * centeredPrimitive x at he
  rw [he]
  calc
    _ ≤ |v b * centeredPrimitive b| + |v a * centeredPrimitive a| +
        |∫ x in a..b, v' x * centeredPrimitive x| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (-v b) / 16 + (-v a) / 16 + (v b - v a) / 16 := by
      gcongr
      · rw [abs_mul, abs_of_nonpos (hn b ⟨hab, le_rfl⟩)]
        exact (mul_le_mul_of_nonneg_left (centered_primitive_bound b)
          (neg_nonneg.mpr (hn b ⟨hab, le_rfl⟩))).trans_eq (by ring)
      · rw [abs_mul, abs_of_nonpos (hn a ⟨le_rfl, hab⟩)]
        exact (mul_le_mul_of_nonneg_left (centered_primitive_bound a)
          (neg_nonneg.mpr (hn a ⟨le_rfl, hab⟩))).trans_eq (by ring)
    _ = _ := by ring

/-- The original statement is preserved for all existing consumers. -/
private lemma bernoulli_residual_bound {a b : ℝ} {v v' : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hv : ∀ x ∈ Icc a b, HasDerivAt v (v' x) x)
    (hc : ContinuousOn v' (Icc a b))
    (hn : ∀ x ∈ Icc a b, v x ≤ 0)
    (hp : ∀ x ∈ Icc a b, 0 ≤ v' x) :
    |∫ x in a..b, v x * betaOne x| ≤ -v a / 6 := by
  exact (centered_negative_bound ha hab hv hc hn hp).trans
    (by have := hn a ⟨le_rfl, hab⟩; linarith)

/-- The original kernel denominator. -/
def normalization (t : ℝ) : ℝ := weight t * t ^ (11 / 10 : ℝ)

/-- The smooth body extends across the excluded initial point. -/
def smoothBody (t d x : ℝ) : ℝ :=
  Real.log (x / d) * (g x - g (endpoint t)) / normalization t

def weightSlope (x : ℝ) : ℝ :=
  (MellinWeightedVariation.scaleDerivative x 1 - weight x) / x

private def bodySlope (t d x : ℝ) : ℝ :=
  ((g x - g (endpoint t)) / x - Real.log (x / d) * weight x) / normalization t

private def bodySecond (t d x : ℝ) : ℝ :=
  (-(g x - g (endpoint t)) / x ^ 2 - 2 * weight x / x -
    Real.log (x / d) * weightSlope x) / normalization t

private lemma normalization_pos {t : ℝ} (ht : 1 < t) : 0 < normalization t := by
  exact mul_pos (OriginalMovingWindowMoment.weight_pos ht)
    (Real.rpow_pos_of_pos (by linarith) _)

private lemma weight_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt weight (weightSlope x) x := by
  have hx0 : 0 < x := by linarith
  have hd := (MellinWeightedVariation.hasDerivAt_scaleWeight (y := 1) hx0
    (by norm_num) (by simpa using hx)).div (hasDerivAt_id x) hx0.ne'
  have he : (fun s : ℝ => MellinWeightedVariation.scaleWeight s 1 / s) =ᶠ[𝓝 x] weight := by
    filter_upwards [eventually_ne_nhds hx0.ne'] with s hs
    rw [MellinWeightedVariation.scaleWeight_eq, mul_one, mul_div_cancel_left₀ _ hs]
  exact (hd.congr_of_eventuallyEq he.symm).congr_deriv (by
    simp only [id_eq, mul_one, MellinWeightedVariation.scaleWeight_eq]
    dsimp only [weightSlope]
    field_simp [hx0.ne']
    <;> ring)

private lemma log_quotient_deriv {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Real.log (y / d)) (1 / x) x := by
  exact (((hasDerivAt_id x).div_const d).log (div_pos hx hd).ne').congr_deriv (by
    simp only [id_eq]
    field_simp [hx.ne', hd.ne'])

private lemma smooth_body_deriv {t d x : ℝ} (hd : 0 < d) (hx : 1 < x) :
    HasDerivAt (smoothBody t d) (bodySlope t d x) x := by
  have hg := ActualRobinClockCovariance.g_has_deriv_at hx
  change HasDerivAt g (-weight x) x at hg
  have h : HasDerivAt (smoothBody t d)
      ((1 / x * (g x - g (endpoint t)) + Real.log (x / d) * (-weight x)) /
        normalization t) x := by
    simpa only [smoothBody, Pi.mul_apply] using!
      ((log_quotient_deriv hd (by linarith)).mul
        (hg.sub_const (g (endpoint t)))).div_const (normalization t)
  exact h.congr_deriv (by dsimp only [bodySlope]; ring)

private lemma body_slope_deriv {t d x : ℝ} (hd : 0 < d) (hx : 1 < x) :
    HasDerivAt (bodySlope t d) (bodySecond t d x) x := by
  have hg := ActualRobinClockCovariance.g_has_deriv_at hx
  change HasDerivAt g (-weight x) x at hg
  have h0 : x ≠ 0 := by linarith
  have h : HasDerivAt (bodySlope t d)
      (((-weight x * x - (g x - g (endpoint t))) / x ^ 2 -
        (1 / x * weight x + Real.log (x / d) * weightSlope x)) / normalization t) x := by
    simpa only [bodySlope, Pi.sub_apply, Pi.div_apply, Pi.mul_apply, id_eq, mul_one] using!
      (((hg.sub_const (g (endpoint t))).div (hasDerivAt_id x) h0).sub
        ((log_quotient_deriv hd (by linarith)).mul (weight_deriv hx))).div_const
          (normalization t)
  exact h.congr_deriv (by dsimp only [bodySecond]; field_simp; ring)

private lemma weight_slope_bound {x : ℝ} (hx : 1 < x) :
    weightSlope x ≤ -2 * weight x / x := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_pos hx
  have hp : 0 ≤ (Real.log x)⁻¹ ^ 2 + 2 * (Real.log x)⁻¹ ^ 3 := by positivity
  unfold weightSlope MellinWeightedVariation.scaleDerivative weight
  simp only [mul_one, one_pow]
  apply (div_le_div_iff_of_pos_right hx0).mpr
  have hnorm :
      -((Real.log x)⁻¹ + 2 * (Real.log x)⁻¹ ^ 2 + 2 * (Real.log x)⁻¹ ^ 3) /
        x ^ 2 - (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) =
      -2 * ((Real.log x + 1) / (x ^ 2 * Real.log x ^ 2)) -
        ((Real.log x)⁻¹ ^ 2 + 2 * (Real.log x)⁻¹ ^ 3) / x ^ 2 := by
    field_simp
    <;> ring
  rw [hnorm]
  exact sub_le_self _ (div_nonneg hp (sq_nonneg x))

/-- Exact phases and derivative variation for arbitrary real endpoints above one. -/
theorem weighted_bernoulli_phase {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, weight x * betaOne x) =
      weight b * centeredPrimitive b - weight a * centeredPrimitive a -
        (∫ x in a..b, weightSlope x * centeredPrimitive x) ∧
    |(∫ x in a..b, weight x * betaOne x) -
      (weight b * centeredPrimitive b - weight a * centeredPrimitive a)| ≤
        (weight a - weight b) / 16 ∧
    |∫ x in a..b, weight x * betaOne x| ≤ weight a / 8 := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt weight (weightSlope x) x :=
    fun x hx => weight_deriv (ha.trans_le hx.1)
  have hc : ContinuousOn weightSlope (Icc a b) := by
    intro x hx
    have hx1 := ha.trans_le hx.1
    have hx0 : x ≠ 0 := by linarith
    have hl : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    unfold weightSlope MellinWeightedVariation.scaleDerivative weight
    simp only [mul_one, one_pow]
    fun_prop (disch := aesop)
  have hs : ∀ x ∈ Icc a b, weightSlope x ≤ 0 := by
    intro x hx
    have hx1 := ha.trans_le hx.1
    exact (weight_slope_bound hx1).trans (by
      have hw := MellinWeightedVariation.weight_nonneg hx1
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hi : IntervalIntegrable weightSlope volume a b :=
    (uIcc_of_le hab ▸ hc).intervalIntegrable
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hd x (uIcc_of_le hab ▸ hx)) hi
  have hr : |∫ x in a..b, weightSlope x * centeredPrimitive x| ≤
      (weight a - weight b) / 16 := by
    rw [← Real.norm_eq_abs]
    calc
      _ ≤ ∫ x in a..b, -weightSlope x / 16 := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · filter_upwards [] with x hx
          have hn := hs x ⟨hx.1.le, hx.2⟩
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
          exact (mul_le_mul_of_nonneg_left (centered_primitive_bound x)
            (neg_nonneg.mpr hn)).trans_eq (by ring)
        · exact hi.neg.div_const 16
      _ = _ := by rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, hft]; ring
  have he := primitive_parts (by linarith : 0 ≤ a) hab hd hc (1 / 48)
  change (∫ x in a..b, weight x * betaOne x) =
    weight b * centeredPrimitive b - weight a * centeredPrimitive a -
      (∫ x in a..b, weightSlope x * centeredPrimitive x) at he
  refine ⟨he, ?_, ?_⟩
  · rw [he, sub_sub_cancel_left, abs_neg]
    exact hr
  · have hn := centered_negative_bound (v := fun x => -weight x)
      (v' := fun x => -weightSlope x) (by linarith : 0 ≤ a) hab
      (fun x hx => (hd x hx).neg) hc.neg
      (fun x hx => neg_nonpos.mpr (MellinWeightedVariation.weight_nonneg
        (ha.trans_le hx.1))) (fun x hx => neg_nonneg.mpr (hs x hx))
    simpa only [neg_mul, intervalIntegral.integral_neg, abs_neg, neg_neg] using hn

private lemma width_le {t : ℝ} (ht : 1 ≤ t) : width t ≤ t := by
  simpa only [width, Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le ht (show (4 / 5 : ℝ) ≤ 1 by norm_num))

private lemma body_slope_signs {t d x : ℝ} (ht : 4 ≤ t) (hd : 0 < d)
    (hlog : 2 ≤ Real.log (t / d)) (hx : x ∈ Icc t (endpoint t)) :
    bodySlope t d x ≤ 0 ∧ 0 ≤ bodySecond t d x := by
  have hx1 : 1 < x := by linarith [hx.1]
  have hx0 : 0 < x := by linarith
  have hwt := OriginalMovingWindowMoment.weight_pos hx1
  have hn := normalization_pos (t := t) (by linarith)
  have hl : 2 ≤ Real.log (x / d) := hlog.trans
    (Real.log_le_log (div_pos (by linarith) hd)
      (div_le_div_of_nonneg_right hx.1 hd.le))
  have hg := OriginalMovingWindowMoment.price_drop (t := x) (ht.trans hx.1) le_rfl hx.2
  have hwidth := width_le (t := t) (by linarith)
  have hspan : endpoint t - x ≤ x := by dsimp [endpoint] at *; linarith [hx.1]
  have hdrop : g x - g (endpoint t) ≤ weight x * x :=
    hg.2.trans (mul_le_mul_of_nonneg_left hspan hwt.le)
  have hd0 : 0 ≤ g x - g (endpoint t) := by
    have h := mul_nonneg (OriginalMovingWindowMoment.weight_pos
      (by linarith [hx.2] : 1 < endpoint t)).le (sub_nonneg.mpr hx.2)
    exact h.trans hg.1
  have hws := weight_slope_bound hx1
  constructor
  · apply div_nonpos_of_nonpos_of_nonneg _ hn.le
    have hquot : (g x - g (endpoint t)) / x ≤ weight x :=
      (div_le_iff₀ hx0).mpr hdrop
    have hmul : weight x ≤ Real.log (x / d) * weight x := by nlinarith
    exact sub_nonpos.mpr (hquot.trans hmul)
  · apply div_nonneg _ hn.le
    have hquot : (g x - g (endpoint t)) / x ^ 2 ≤ weight x / x := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hx0) hx0).mpr
      nlinarith [mul_le_mul_of_nonneg_right hdrop hx0.le]
    have hmul := mul_le_mul_of_nonneg_left hws (by linarith : 0 ≤ Real.log (x / d))
    have hquotpos : 0 < weight x / x := div_pos hwt hx0
    have hr : Real.log (x / d) * (-2 * weight x / x) =
        -2 * Real.log (x / d) * (weight x / x) := by ring
    rw [hr] at hmul
    have hgrowth := mul_le_mul_of_nonneg_right hl hquotpos.le
    rw [neg_div, mul_div_assoc]
    nlinarith



/-- The signed height of the smooth extension at the initial point. -/
def boundaryHeight (t : ℝ) : ℝ := (g t - g (endpoint t)) / normalization t

/-- All positive cofactor rows up to the genuine terminal floor. -/
def latticeValue (t : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 ⌊endpoint t / d⌋₊, Real.log m * kernel t (d * m)

/-- The original continuous cofactor row, using the literal kernel. -/
def continuousValue (t : ℝ) (d : ℕ) : ℝ :=
  (1 / d) * ∫ x in t..endpoint t, Real.log (x / d) * kernel t x

private lemma body_second_continuous {t d a b : ℝ} (ha : 1 < a) (hd : 0 < d) :
    ContinuousOn (bodySecond t d) (Icc a b) := by
  intro x hx
  have hx1 := ha.trans_le hx.1
  have hx0 : x ≠ 0 := by linarith
  have hl0 := (Real.log_pos hx1).ne'
  have hd0 := hd.ne'
  apply ContinuousAt.continuousWithinAt
  unfold bodySecond
  apply ContinuousAt.div_const
  unfold weightSlope g weight MellinWeightedVariation.scaleDerivative
  simp only [mul_one, one_pow]
  fun_prop (disch := aesop)

private lemma smooth_quadrature_residual {t d : ℝ} (ht : 4 ≤ t) (hd : 0 < d)
    (hlog : 2 ≤ Real.log (t / d)) :
    |(∑ m ∈ Finset.Ioc ⌊t / d⌋₊ ⌊endpoint t / d⌋₊, smoothBody t d (d * m)) -
      (1 / d) * (∫ x in t..endpoint t, smoothBody t d x) -
      boundaryHeight t * Real.log (t / d) * betaOne (t / d)| ≤
      d / 6 * (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) := by
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := by
    dsimp [endpoint, width]
    have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
    linarith
  have hab := div_le_div_of_nonneg_right htb hd.le
  let F : ℝ → ℝ := fun y => smoothBody t d (d * y)
  let V : ℝ → ℝ := fun y => d * bodySlope t d (d * y)
  let V' : ℝ → ℝ := fun y => d ^ 2 * bodySecond t d (d * y)
  have hx (y : ℝ) (hy : y ∈ Icc (t / d) (endpoint t / d)) :
      d * y ∈ Icc t (endpoint t) := by
    constructor
    · simpa only [mul_comm d y] using (div_le_iff₀ hd).mp hy.1
    · simpa only [mul_comm d y] using (le_div_iff₀ hd).mp hy.2
  have hF (y : ℝ) (hy : y ∈ Icc (t / d) (endpoint t / d)) :
      HasDerivAt F (V y) y := by
    have h := (smooth_body_deriv (t := t) hd (by simp only [id_eq]; have hm := (hx y hy).1; linarith)).comp y
      ((hasDerivAt_id y).const_mul d)
    convert h using 1 <;> first | rfl | (dsimp [F, V]; ring)
  have hV (y : ℝ) (hy : y ∈ Icc (t / d) (endpoint t / d)) :
      HasDerivAt V (V' y) y := by
    have h := ((body_slope_deriv (t := t) hd (by simp only [id_eq]; have hm := (hx y hy).1; linarith)).comp y
      ((hasDerivAt_id y).const_mul d)).const_mul d
    convert h using 1 <;> first | rfl | (dsimp [V, V']; ring)
  have hVc : ContinuousOn V (uIcc (t / d) (endpoint t / d)) := by
    rw [uIcc_of_le hab]
    exact fun y hy => (hV y hy).continuousAt.continuousWithinAt
  have hV'c : ContinuousOn V' (Icc (t / d) (endpoint t / d)) := by
    apply continuousOn_const.mul
    exact (body_second_continuous (t := t) (d := d) (a := t) (b := endpoint t)
      (by linarith) hd).comp (continuousOn_const.mul continuousOn_id) hx
  have hres := bernoulli_residual_bound (v := V) (v' := V')
    (div_pos ht0 hd).le hab hV hV'c
    (fun y hy => mul_nonpos_of_nonneg_of_nonpos hd.le
      (body_slope_signs ht hd hlog (hx y hy)).1)
    (fun y hy => mul_nonneg (sq_nonneg d)
      (body_slope_signs ht hd hlog (hx y hy)).2)
  have hderiv : ∀ y ∈ Icc (t / d) (endpoint t / d), deriv F y = V y :=
    fun y hy => (hF y hy).deriv
  have hc : ContinuousOn (deriv F) (uIcc (t / d) (endpoint t / d)) := by
    apply hVc.congr
    intro y hy
    exact hderiv y (uIcc_of_le hab ▸ hy)
  have heuler := sum_eq_integral_add_integral_deriv (f := F)
    (div_pos ht0 hd).le hab (fun y hy => (hF y hy).differentiableAt) hc
  simp only [RCLike.ofReal_real_eq_id, id_eq] at heuler
  have hint : (∫ y in (t / d)..(endpoint t / d), deriv F y * B1 y) =
      ∫ y in (t / d)..(endpoint t / d), V y * betaOne y := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hab] at hy
    dsimp only
    rw [hderiv y hy, beta_eq_B1 ((div_pos ht0 hd).le.trans hy.1)]
  have hFa : F (t / d) = boundaryHeight t * Real.log (t / d) := by
    dsimp [F, smoothBody, boundaryHeight]
    rw [mul_div_cancel₀ _ hd.ne']
    ring
  have hFb : F (endpoint t / d) = 0 := by
    dsimp [F, smoothBody]
    rw [mul_div_cancel₀ _ hd.ne']
    ring
  have hFi : (∫ y in (t / d)..(endpoint t / d), F y) =
      (1 / d) * ∫ x in t..endpoint t, smoothBody t d x := by
    dsimp only [F]
    rw [intervalIntegral.integral_comp_mul_left _ hd.ne',
      mul_div_cancel₀ _ hd.ne', mul_div_cancel₀ _ hd.ne']
    simp [smul_eq_mul, one_div]
  rw [hint, hFa, hFb, hFi, zero_mul, sub_zero,
    ← beta_eq_B1 (div_pos ht0 hd).le] at heuler
  have hVa : -V (t / d) / 6 =
      d / 6 * (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) := by
    dsimp [V, bodySlope, boundaryHeight, normalization]
    rw [mul_div_cancel₀ _ hd.ne', show (-11 / 10 : ℝ) = -(11 / 10 : ℝ) by ring, Real.rpow_neg ht0.le]
    field_simp [(OriginalMovingWindowMoment.weight_pos (by linarith : 1 < t)).ne',
      ht0.ne', (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ)).ne']
    <;> ring
  rw [hVa] at hres
  convert hres using 1
  rw [heuler]
  congr 1
  ring



private lemma lattice_eq_smooth {t : ℝ} {d : ℕ} (ht : 4 ≤ t) (hd : 1 ≤ d) :
    latticeValue t d =
      ∑ m ∈ Finset.Ioc ⌊t / d⌋₊ ⌊endpoint t / d⌋₊, smoothBody t d (d * m) := by
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := by
    dsimp [endpoint, width]
    have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
    linarith
  have hb0 : 0 ≤ endpoint t / d := div_nonneg (ht0.le.trans htb) hd0.le
  have hsub : Finset.Ioc ⌊t / d⌋₊ ⌊endpoint t / d⌋₊ ⊆
      Finset.Icc 1 ⌊endpoint t / d⌋₊ := by
    intro m hm
    simp only [Finset.mem_Ioc, Finset.mem_Icc] at *
    omega
  have hs := Finset.sum_subset hsub (f := fun m : ℕ => Real.log m * kernel t (d * m))
    (fun m hm hn => by
      have hm' := Finset.mem_Icc.mp hm
      have hmlo : m ≤ ⌊t / d⌋₊ := by
        have hnot : ¬ ⌊t / d⌋₊ < m := fun hh => hn (Finset.mem_Ioc.mpr ⟨hh, hm'.2⟩)
        omega
      have hmt := (Nat.le_floor_iff (div_pos ht0 hd0).le).mp hmlo
      have hdm : (d : ℝ) * m ≤ t := by
        simpa only [mul_comm] using (le_div_iff₀ hd0).mp hmt
      have hk : kernel t (d * m) = 0 := by
        unfold kernel
        rw [if_neg (by rintro ⟨h, _⟩; linarith)]
      rw [hk, mul_zero])
  unfold latticeValue
  rw [← hs]
  apply Finset.sum_congr rfl
  intro m hm
  have hm' := Finset.mem_Ioc.mp hm
  have hmt : t / d < m := (Nat.floor_lt (div_pos ht0 hd0).le).mp hm'.1
  have hmb : (m : ℝ) ≤ endpoint t / d := (Nat.le_floor_iff hb0).mp hm'.2
  have hl : t < (d : ℝ) * m := by
    simpa only [mul_comm] using (div_lt_iff₀ hd0).mp hmt
  have hu : (d : ℝ) * m ≤ endpoint t := by
    simpa only [mul_comm] using (le_div_iff₀ hd0).mp hmb
  dsimp [smoothBody, kernel, normalization]
  rw [if_pos ⟨hl, hu⟩, mul_div_cancel_left₀ _ hd0.ne']
  ring

private lemma continuous_eq_smooth {t : ℝ} {d : ℕ} (ht : 4 ≤ t) :
    continuousValue t d = (1 / d) * ∫ x in t..endpoint t, smoothBody t d x := by
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := by
    dsimp [endpoint, width]
    have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
    linarith
  unfold continuousValue
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x hx
  rw [uIoc_of_le htb] at hx
  dsimp [smoothBody, kernel, normalization]
  rw [if_pos (show t < x ∧ x ≤ endpoint t from hx)]
  ring

private lemma early_log_bound {t : ℝ} {d : ℕ} (ht : 256 ≤ t) (hd : 1 ≤ d)
    (hD : d ≤ ⌊t ^ (151 / 500 : ℝ)⌋₊) : 2 ≤ Real.log (t / d) := by
  have ht0 : 0 < t := by linarith
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
  have hdp : (d : ℝ) ≤ t ^ (151 / 500 : ℝ) :=
    (Nat.le_floor_iff (Real.rpow_nonneg ht0.le _)).mp hD
  have hld := Real.log_le_log hd0 hdp
  rw [Real.log_rpow ht0] at hld
  have h4 := OriginalMovingWindowMoment.log_large (x := 4) (by norm_num)
  have h256 := Real.log_pow (4 : ℝ) 4
  norm_num at h256
  have hlt := Real.log_le_log (by norm_num : (0 : ℝ) < 256) ht
  rw [Real.log_div ht0.ne' hd0.ne']
  linarith

/-- The exact original early-divisor cutoff. -/
def divisorCutoff (t : ℝ) : ℕ := ⌊t ^ (151 / 500 : ℝ)⌋₊

/-- All signed early cofactor rows, including every zero Möbius coefficient. -/
def earlyError (t : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (divisorCutoff t),
    (ArithmeticFunction.moebius d : ℝ) * (latticeValue t d - continuousValue t d)

/-- The signed initial Bernoulli endpoint sum. -/
def endpointSum (t : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (divisorCutoff t),
    (ArithmeticFunction.moebius d : ℝ) * Real.log (t / d) * betaOne (t / d)

/-- The second-order residual is controlled by actual initial slope brackets. -/
private theorem original_early_residual {t : ℝ} (ht : 256 ≤ t) :
    |earlyError t - boundaryHeight t * endpointSum t| ≤
      (1 / 6 : ℝ) * ∑ d ∈ Finset.Icc 1 (divisorCutoff t),
        |(ArithmeticFunction.moebius d : ℝ)| * d *
          (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) := by
  have hrow (d : ℕ) (hd : d ∈ Finset.Icc 1 (divisorCutoff t)) :
      |latticeValue t d - continuousValue t d -
        boundaryHeight t * Real.log (t / d) * betaOne (t / d)| ≤
      (d : ℝ) / 6 *
        (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) := by
    have hd' := Finset.mem_Icc.mp hd
    have hr := smooth_quadrature_residual (t := t) (d := d) (by linarith)
      (by exact_mod_cast hd'.1) (early_log_bound ht hd'.1 hd'.2)
    rwa [← lattice_eq_smooth (by linarith) hd'.1,
      ← continuous_eq_smooth (d := d) (by linarith)] at hr
  have heq : earlyError t - boundaryHeight t * endpointSum t =
      ∑ d ∈ Finset.Icc 1 (divisorCutoff t), (ArithmeticFunction.moebius d : ℝ) *
        (latticeValue t d - continuousValue t d -
          boundaryHeight t * Real.log (t / d) * betaOne (t / d)) := by
    unfold earlyError endpointSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 (divisorCutoff t),
        |(ArithmeticFunction.moebius d : ℝ) *
          (latticeValue t d - continuousValue t d -
            boundaryHeight t * Real.log (t / d) * betaOne (t / d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (divisorCutoff t),
        |(ArithmeticFunction.moebius d : ℝ)| * ((d : ℝ) / 6 *
          (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hrow d hd) (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring



private lemma boundary_nonneg {t : ℝ} (ht : 4 ≤ t) : 0 ≤ boundaryHeight t := by
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := by
    dsimp [endpoint, width]
    have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
    linarith
  have hg := OriginalMovingWindowMoment.price_drop ht le_rfl htb
  apply div_nonneg _ (normalization_pos (by linarith : 1 < t)).le
  exact (mul_nonneg (OriginalMovingWindowMoment.weight_pos
    (by linarith : 1 < endpoint t)).le (sub_nonneg.mpr htb)).trans hg.1

/-- Each original slope bracket is nonnegative and the complete smooth remainder decays. -/
private theorem original_early_residual_decay {t : ℝ} (ht : 256 ≤ t) :
    (∀ d ∈ Finset.Icc 1 (divisorCutoff t),
      0 ≤ Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) ∧
    |earlyError t - boundaryHeight t * endpointSum t| ≤
      (1 / 6 : ℝ) * t ^ (-62 / 125 : ℝ) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have hb := boundary_nonneg (t := t) (by linarith)
  have hbr (d : ℕ) (hd : d ∈ Finset.Icc 1 (divisorCutoff t)) :
      0 ≤ Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t := by
    have hd' := Finset.mem_Icc.mp hd
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd'.1
    have hs := (body_slope_signs (t := t) (d := d) (x := t) (by linarith) hd0
      (early_log_bound ht hd'.1 hd'.2) ⟨le_rfl, by
        dsimp [endpoint, width]
        have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
        linarith⟩).1
    have he : -bodySlope t d t =
        Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t := by
      dsimp [bodySlope, boundaryHeight, normalization]
      rw [show (-11 / 10 : ℝ) = -(11 / 10 : ℝ) by ring, Real.rpow_neg ht0.le]
      field_simp [(OriginalMovingWindowMoment.weight_pos (by linarith : 1 < t)).ne',
        ht0.ne', (Real.rpow_pos_of_pos ht0 (11 / 10 : ℝ)).ne']
      <;> ring
    rw [← he]
    linarith
  refine ⟨hbr, (original_early_residual ht).trans ?_⟩
  have hbound : (∑ d ∈ Finset.Icc 1 (divisorCutoff t),
      |(ArithmeticFunction.moebius d : ℝ)| * d *
        (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t)) ≤
      (divisorCutoff t : ℝ) ^ 2 * (Real.log t * t ^ (-11 / 10 : ℝ)) := by
    calc
      _ ≤ ∑ _d ∈ Finset.Icc 1 (divisorCutoff t),
          (divisorCutoff t : ℝ) * (Real.log t * t ^ (-11 / 10 : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        have hd' := Finset.mem_Icc.mp hd
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd'.1
        have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        have hlog := Real.log_le_log (div_pos ht0 (by linarith))
          ((div_le_self ht0.le hd1))
        have hupper : Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t ≤
            Real.log t * t ^ (-11 / 10 : ℝ) := by
          have hp := Real.rpow_nonneg ht0.le (-11 / 10 : ℝ)
          have hterm := mul_le_mul_of_nonneg_right hlog hp
          have hbq := div_nonneg hb ht0.le
          linarith
        have hcoeff : |(ArithmeticFunction.moebius d : ℝ)| * d ≤ divisorCutoff t := by
          calc
            _ ≤ 1 * (d : ℝ) := mul_le_mul_of_nonneg_right hmu (Nat.cast_nonneg _)
            _ ≤ _ := by simpa only [one_mul] using (Nat.cast_le.mpr hd'.2 : (d : ℝ) ≤ _)
        exact mul_le_mul hcoeff hupper (hbr d hd) (Nat.cast_nonneg _)
      _ = _ := by simp [Nat.card_Icc]; ring
  have hD : (divisorCutoff t : ℝ) ≤ t ^ (151 / 500 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg ht0.le _)
  have hD2 : (divisorCutoff t : ℝ) ^ 2 ≤ t ^ (302 / 500 : ℝ) := by
    calc
      _ ≤ (t ^ (151 / 500 : ℝ)) ^ 2 := by gcongr
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
  have hlog0 := (Real.log_pos (show 1 < t by linarith)).le
  have hh : (divisorCutoff t : ℝ) ^ 2 * (Real.log t * t ^ (-11 / 10 : ℝ)) ≤
      t ^ (-62 / 125 : ℝ) * Real.log t := by
    calc
      _ ≤ t ^ (302 / 500 : ℝ) * (Real.log t * t ^ (-11 / 10 : ℝ)) := by gcongr
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add ht0]; norm_num; ring
  calc
    _ ≤ (1 / 6 : ℝ) * ((divisorCutoff t : ℝ) ^ 2 *
        (Real.log t * t ^ (-11 / 10 : ℝ))) := by gcongr
    _ ≤ (1 / 6 : ℝ) * (t ^ (-62 / 125 : ℝ) * Real.log t) := by gcongr
    _ = _ := by ring



/-- The exact centering of the original moving window. -/
def centering (t : ℝ) : ℝ :=
  (Real.log (Real.log (endpoint t)) - Real.log (Real.log t) - width t * g (endpoint t)) /
    normalization t

/-- The all-power finite von Mangoldt readout of the literal moving window. -/
def discretePhi (t : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊endpoint t⌋₊,
    ArithmeticFunction.vonMangoldt n * kernel t n) - centering t

/-- Only the early rows are integrated; every remaining cofactor row is retained. -/
def mixedG (t : ℝ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 (divisorCutoff t),
    (ArithmeticFunction.moebius d : ℝ) * continuousValue t d) +
  (∑ d ∈ Finset.Ioc (divisorCutoff t) ⌊endpoint t⌋₊,
    (ArithmeticFunction.moebius d : ℝ) * latticeValue t d) - centering t

private lemma finite_mobius_reconstruction (N : ℕ) (F : ℕ → ℝ)
    (hF : ∀ n, N < n → F n = 0) :
    (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ) * Real.log m * F (d * m)) =
      ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * F n := by
  classical
  let B := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)
  let S := B.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N)
  let W := fun p : ℕ × ℕ => (ArithmeticFunction.moebius p.1 : ℝ) * Real.log p.2 * F (p.1 * p.2)
  have htrim : (∑ p ∈ B, W p) = ∑ p ∈ S, W p := by
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 * p.2 ≤ N
    · simp [h]
    · simp [h, W, hF _ (lt_of_not_ge h)]
  have hmaps : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 N := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpB, hpN⟩
    rcases Finset.mem_product.mp hpB with ⟨hd, hm⟩
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos
      (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hm).1, hpN⟩
  have hfiber (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      S.filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
    ext p
    constructor
    · intro hp
      exact Nat.mem_divisorsAntidiagonal.mpr
        ⟨(Finset.mem_filter.mp hp).2, ne_of_gt (Finset.mem_Icc.mp hn).1⟩
    · intro hp
      obtain ⟨he, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hprod : 0 < p.1 * p.2 := by rw [he]; exact (Finset.mem_Icc.mp hn).1
      have hd : 0 < p.1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hprod)
      have hm : 0 < p.2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hprod)
      have hpN : p.1 * p.2 ≤ N := by rw [he]; exact (Finset.mem_Icc.mp hn).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hd, (Nat.le_mul_of_pos_right _ hm).trans hpN⟩,
            Finset.mem_Icc.mpr ⟨hm, (Nat.le_mul_of_pos_left _ hd).trans hpN⟩⟩, hpN⟩, he⟩
  calc
    _ = ∑ p ∈ B, W p := by simp only [B, W, Finset.sum_product]
    _ = ∑ p ∈ S, W p := htrim
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ S with p.1 * p.2 = n, W p :=
      (Finset.sum_fiberwise_of_maps_to hmaps W).symm
    _ = ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * F n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfiber n hn]
      calc
        _ = ∑ p ∈ n.divisorsAntidiagonal,
            ((ArithmeticFunction.moebius p.1 : ℝ) * Real.log p.2) * F n := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [W]
          rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
        _ = (∑ p ∈ n.divisorsAntidiagonal,
            (ArithmeticFunction.moebius p.1 : ℝ) * Real.log p.2) * F n := by
          rw [Finset.sum_mul]
        _ = ArithmeticFunction.vonMangoldt n * F n := by
          have he := congrArg (fun a : ArithmeticFunction ℝ => a n)
            ArithmeticFunction.moebius_mul_log_eq_vonMangoldt
          simpa only [ArithmeticFunction.mul_apply, ArithmeticFunction.intCoe_apply,
            ArithmeticFunction.log_apply] using congrArg (fun x : ℝ => x * F n) he

private lemma full_row_reconstruction {t : ℝ} (ht : 4 ≤ t) :
    discretePhi t =
      (∑ d ∈ Finset.Icc 1 ⌊endpoint t⌋₊,
        (ArithmeticFunction.moebius d : ℝ) * latticeValue t d) - centering t := by
  have ht0 : 0 < t := by linarith
  have htb : t ≤ endpoint t := by
    dsimp [endpoint, width]
    have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
    linarith
  have hb0 : 0 < endpoint t := ht0.trans_le htb
  have hzero (n : ℕ) (hn : ⌊endpoint t⌋₊ < n) : kernel t n = 0 := by
    have hnB : endpoint t < n := (Nat.floor_lt hb0.le).mp hn
    unfold kernel
    rw [if_neg (by rintro ⟨_, h⟩; linarith)]
  have hconv := finite_mobius_reconstruction ⌊endpoint t⌋₊ (fun n => kernel t n) hzero
  unfold discretePhi
  rw [← hconv]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd1
  have hcut : ⌊endpoint t / d⌋₊ ≤ ⌊endpoint t⌋₊ :=
    Nat.floor_mono (div_le_self hb0.le (by exact_mod_cast hd1))
  rw [latticeValue, Finset.mul_sum]
  simp only [Nat.cast_mul, mul_assoc]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hcut)
  intro m hm hn
  have hm1 := (Finset.mem_Icc.mp hm).1
  have hmcut : ⌊endpoint t / d⌋₊ < m := by
    have hh : ¬ m ≤ ⌊endpoint t / d⌋₊ := fun hh => hn (Finset.mem_Icc.mpr ⟨hm1, hh⟩)
    omega
  have hmB := (Nat.floor_lt (div_pos hb0 hd0).le).mp hmcut
  have hdm : endpoint t < (d : ℝ) * m := by
    simpa only [mul_comm] using (div_lt_iff₀ hd0).mp hmB
  have hk : kernel t ((d : ℝ) * m) = 0 := by
    unfold kernel
    rw [if_neg (by rintro ⟨_, h⟩; linarith)]
  simp only [hk, mul_zero]

private lemma cutoff_within {t : ℝ} (ht : 4 ≤ t) : divisorCutoff t ≤ ⌊endpoint t⌋₊ := by
  have ht0 : 0 < t := by linarith
  apply Nat.floor_mono
  calc
    t ^ (151 / 500 : ℝ) ≤ t ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ ≤ endpoint t := by
      rw [Real.rpow_one]
      dsimp [endpoint, width]
      have hp := Real.rpow_nonneg ht0.le (4 / 5 : ℝ)
      linarith

private lemma phi_eq_mixed_add_early {t : ℝ} (ht : 4 ≤ t) :
    discretePhi t = mixedG t + earlyError t := by
  rw [full_row_reconstruction ht]
  have hsplit := Finset.sum_Ioc_consecutive
    (fun d => (ArithmeticFunction.moebius d : ℝ) * latticeValue t d)
    (Nat.zero_le (divisorCutoff t)) (cutoff_within ht)
  have hsum :
      (∑ d ∈ Finset.Icc 1 (divisorCutoff t), (ArithmeticFunction.moebius d : ℝ) * latticeValue t d) +
      (∑ d ∈ Finset.Ioc (divisorCutoff t) ⌊endpoint t⌋₊, (ArithmeticFunction.moebius d : ℝ) * latticeValue t d) =
      ∑ d ∈ Finset.Icc 1 ⌊endpoint t⌋₊, (ArithmeticFunction.moebius d : ℝ) * latticeValue t d := by
    have hI (n : ℕ) : Finset.Ioc 0 n = Finset.Icc 1 n := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    simpa only [hI] using hsplit
  unfold mixedG earlyError
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

/-- The literal all-power readout consumes the signed early quadrature estimate. -/
theorem original_early_quadrature {t : ℝ} (ht : 256 ≤ t) :
    discretePhi t = mixedG t + earlyError t ∧
    (∀ d ∈ Finset.Icc 1 (divisorCutoff t),
      0 ≤ Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) ∧
    |discretePhi t - mixedG t - boundaryHeight t * endpointSum t| ≤
      (1 / 6 : ℝ) * ∑ d ∈ Finset.Icc 1 (divisorCutoff t),
        |(ArithmeticFunction.moebius d : ℝ)| * d *
          (Real.log (t / d) * t ^ (-11 / 10 : ℝ) - boundaryHeight t / t) ∧
    |discretePhi t - mixedG t - boundaryHeight t * endpointSum t| ≤
      (1 / 6 : ℝ) * t ^ (-62 / 125 : ℝ) * Real.log t := by
  have he := phi_eq_mixed_add_early (t := t) (by linarith)
  have hs := original_early_residual_decay ht
  refine ⟨he, hs.1, ?_, ?_⟩
  · rw [he, add_sub_cancel_left]
    exact original_early_residual ht
  · rw [he, add_sub_cancel_left]
    exact hs.2

#print axioms original_early_quadrature

#print axioms weighted_bernoulli_phase

end D5.S3.Arith.Robin.OriginalEarlyDivisorQuadrature
