/- GID: D5/S3/Analytic/PowerSeries/DottieInverseSeries
   generality: I
   mirror-B: D5/B/S3/Analytic/PowerSeries/DottieInverseSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prescribed rational arcsine series and its formal compositional inverse. -/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import D5.S3.Analytic.OriginalHalfBinomialIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import D5.S3.Analytic.PowerSeries.ScalarComposition
import D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

/-! The literal rational coefficients and compositional inverse. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Metric
open scoped Topology PowerSeries NNReal ENNReal

namespace D5.S3.Analytic.PowerSeries.DottieInverseSeries

def alpha (n : ℕ) : ℚ :=
  let k : ℕ := n / 2
  if n % 2 = 0 then 0 else
    (Nat.choose (2 * k) k : ℚ) / ((4 : ℚ) ^ k * ((2 * k + 1 : ℕ) : ℚ))

def arcsine : ℚ⟦X⟧ := PowerSeries.mk alpha

def forward : ℚ⟦X⟧ := 2 * PowerSeries.X + 2 * arcsine

def inverse : ℚ⟦X⟧ := forward.substInvOfIsUnit (by
  have h : PowerSeries.coeff 1 forward = 4 := by
    norm_num [forward, arcsine, alpha]
  rw [h]
  exact isUnit_iff_ne_zero.mpr (by norm_num))

private def sineForward (z : ℂ) : ℂ := z + Complex.sin z

private lemma sin_remainder (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.sin z - z‖ ≤ 1 / 5 := by
  have h₃ : ‖z‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have h₅ : ‖z‖ ^ 5 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  calc
    ‖Complex.sin z - z‖ =
        ‖(Complex.sin z - (z - z ^ 3 / 6)) - z ^ 3 / 6‖ := by congr 1; ring
    _ ≤ ‖Complex.sin z - (z - z ^ 3 / 6)‖ + ‖z ^ 3 / 6‖ := norm_sub_le _ _
    _ ≤ ‖z‖ ^ 5 / 100 + ‖z‖ ^ 3 / 6 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
      linarith [Complex.sin_bound hz]
    _ ≤ 1 / 5 := by linarith

private lemma cos_remainder (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.cos z - 1‖ ≤ 3 / 5 := by
  have h₂ : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  have h₄ : ‖z‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
  calc
    ‖Complex.cos z - 1‖ =
        ‖(Complex.cos z - (1 - z ^ 2 / 2)) - z ^ 2 / 2‖ := by congr 1; ring
    _ ≤ ‖Complex.cos z - (1 - z ^ 2 / 2)‖ + ‖z ^ 2 / 2‖ := norm_sub_le _ _
    _ ≤ ‖z‖ ^ 4 * (5 / 96) + ‖z‖ ^ 2 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
      linarith [Complex.cos_bound hz]
    _ ≤ 3 / 5 := by linarith

private def inverseStep (w z : ℂ) : ℂ := (w + z - Complex.sin z) / 2

private lemma step_maps (w : ℂ) (hw : ‖w‖ < 7 / 4) :
    Set.MapsTo (inverseStep w) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  intro z hz
  simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
  have hs := sin_remainder z hz
  have h : ‖w + z - Complex.sin z‖ ≤ ‖w‖ + 1 / 5 := by
    calc
      _ = ‖w - (Complex.sin z - z)‖ := by congr 1; ring
      _ ≤ ‖w‖ + ‖Complex.sin z - z‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  dsimp [inverseStep]
  rw [norm_div, Complex.norm_ofNat]
  linarith

private lemma step_lipschitz (w : ℂ) :
    LipschitzOnWith (3 / 10) (inverseStep w) (Metric.closedBall 0 1) := by
  apply (convex_closedBall (0 : ℂ) (1 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun z => (1 - Complex.cos z) / 2)
  · intro z hz
    change HasDerivWithinAt (fun t : ℂ => (w + t - Complex.sin t) / 2) _ _ z
    convert
      (((hasDerivAt_const z w).add (hasDerivAt_id z)).sub
        (Complex.hasDerivAt_sin z)).div_const 2 |>.hasDerivWithinAt using 1 <;> simp
  · intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_div, NNReal.coe_ofNat,
      NNReal.coe_ofNat, norm_div, Complex.norm_ofNat, norm_sub_rev]
    have h := cos_remainder z (by simpa using hz)
    linarith

private lemma inverse_exists (w : ℂ) (hw : ‖w‖ < 7 / 4) :
    ∃ z ∈ Metric.ball (0 : ℂ) 1, sineForward z = w := by
  have hm := step_maps w hw
  have hc : ContractingWith (3 / 10) (hm.restrict (inverseStep w) _ _) :=
    ⟨by norm_num, (step_lipschitz w).mapsToRestrict hm⟩
  obtain ⟨z, hz, hfix, _⟩ := hc.exists_fixedPoint'
    isClosed_closedBall.isComplete hm (by simp : (0 : ℂ) ∈ Metric.closedBall 0 1)
    (edist_ne_top _ _)
  have he : sineForward z = w := by
    change (w + z - Complex.sin z) / 2 = z at hfix
    dsimp [sineForward]
    linear_combination -2 * hfix
  refine ⟨z, ?_, he⟩
  simp only [Metric.mem_ball, dist_zero_right]
  have hs := sin_remainder z (by simpa using hz)
  have hn : ‖(2 : ℂ) * z‖ ≤ ‖w‖ + 1 / 5 := by
    calc
      _ = ‖w - (Complex.sin z - z)‖ := by rw [← he]; congr 1; dsimp [sineForward]; ring
      _ ≤ ‖w‖ + ‖Complex.sin z - z‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  rw [norm_mul, Complex.norm_ofNat] at hn
  linarith

private lemma sineForward_inj : Set.InjOn sineForward (Metric.closedBall 0 1) := by
  intro x hx y hy he
  have hxfix : inverseStep (sineForward x) x = x := by dsimp [inverseStep, sineForward]; ring
  have hyfix : inverseStep (sineForward x) y = y := by
    rw [he]
    dsimp [inverseStep, sineForward]
    ring
  have h := (step_lipschitz (sineForward x)).dist_le_mul x hx y hy
  rw [hxfix, hyfix] at h
  have hd : dist x y = 0 := by have := dist_nonneg (x := x) (y := y); norm_num at h; linarith
  exact dist_eq_zero.mp hd

private def selectedInverse (w : ℂ) : ℂ :=
  if hw : ‖w‖ < 7 / 4 then (inverse_exists w hw).choose else 0

private lemma selectedInverse_spec (w : ℂ) (hw : ‖w‖ < 7 / 4) :
    selectedInverse w ∈ Metric.ball 0 1 ∧ sineForward (selectedInverse w) = w := by
  simp only [selectedInverse, dite_eq_left hw]
  exact (inverse_exists w hw).choose_spec

private lemma sineForward_analytic (z : ℂ) : AnalyticAt ℂ sineForward z :=
  analyticAt_id.add Complex.analyticAt_sin

private lemma sineForward_deriv_ne_zero (z : ℂ) (hz : ‖z‖ ≤ 1) :
    deriv sineForward z ≠ 0 := by
  have hd : deriv sineForward z = 1 + Complex.cos z :=
    ((hasDerivAt_id z).add (Complex.hasDerivAt_sin z)).deriv
  rw [hd]
  intro he
  have hcos : Complex.cos z = -1 := by linear_combination he
  have h := cos_remainder z hz
  rw [hcos] at h
  norm_num at h

private lemma selectedInverse_analytic (w : ℂ) (hw : ‖w‖ < 7 / 4) :
    AnalyticAt ℂ selectedInverse w := by
  let x := selectedInverse w
  have hx := selectedInverse_spec w hw
  have ha := sineForward_analytic x
  have hd := sineForward_deriv_ne_zero x (by
    have hxnorm : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx.1
    exact hxnorm.le)
  let l := ha.hasStrictDerivAt.localInverse sineForward (deriv sineForward x) x hd
  have hl : AnalyticAt ℂ l w := by
    rw [← hx.2]
    exact ha.analyticAt_localInverse hd
  have hlx : l w = x := by
    rw [← hx.2]
    exact ha.hasStrictDerivAt.eventually_left_inverse hd |>.self_of_nhds
  have hmem : ∀ᶠ y in 𝓝 w, l y ∈ ball (0 : ℂ) 1 := by
    apply hl.continuousAt.eventually_mem
    rw [hlx]
    exact isOpen_ball.mem_nhds hx.1
  have hright : ∀ᶠ y in 𝓝 w, sineForward (l y) = y := by
    rw [← hx.2]
    exact ha.hasStrictDerivAt.eventually_right_inverse hd
  have hdom : ∀ᶠ y in 𝓝 w, ‖y‖ < 7 / 4 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hw
  apply hl.congr
  filter_upwards [hmem, hright, hdom] with y hly hiy hy
  exact sineForward_inj (ball_subset_closedBall hly)
    (ball_subset_closedBall (selectedInverse_spec y hy).1)
    (hiy.trans (selectedInverse_spec y hy).2.symm)

private lemma selectedInverse_zero : selectedInverse 0 = 0 := by
  have h := selectedInverse_spec 0 (by norm_num)
  exact sineForward_inj (ball_subset_closedBall h.1) (by simp)
    (by simpa [sineForward] using h.2)

private lemma selectedInverse_real (y : ℝ) (hy : |y| < 7 / 4) :
    (selectedInverse y).im = 0 := by
  have h := selectedInverse_spec (y : ℂ) (by simpa using hy)
  have he : sineForward (starRingEnd ℂ (selectedInverse y)) = y := by
    simpa [sineForward, Complex.sin_conj] using congrArg (starRingEnd ℂ) h.2
  have hn : starRingEnd ℂ (selectedInverse y) ∈ closedBall (0 : ℂ) 1 := by
    simpa only [mem_closedBall, dist_zero_right, Complex.norm_conj] using
      ball_subset_closedBall h.1
  have hc := sineForward_inj hn (ball_subset_closedBall h.1) (he.trans h.2.symm)
  have hi := congrArg Complex.im hc
  have hi' : -(selectedInverse y).im = (selectedInverse y).im := by simpa using hi
  linarith

private def endpointFunction (y : ℂ) : ℂ := Complex.sin (selectedInverse (y / 2))

private lemma endpointFunction_analytic (y : ℂ) (hy : ‖y‖ < 7 / 2) :
    AnalyticAt ℂ endpointFunction y := by
  have hr : ‖y / 2‖ < 7 / 4 := by rw [norm_div, Complex.norm_ofNat]; linarith
  have hlin : AnalyticAt ℂ (fun z : ℂ => z / 2) y :=
    (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) y).div_const
  have hsel : AnalyticAt ℂ (fun z : ℂ => selectedInverse (z / 2)) y :=
    AnalyticAt.comp (f := fun z : ℂ => z / 2) (x := y)
      (selectedInverse_analytic (y / 2) hr) hlin
  exact AnalyticAt.comp (f := fun z : ℂ => selectedInverse (z / 2))
    (x := y) Complex.analyticAt_sin hsel

private lemma endpointFunction_zero : endpointFunction 0 = 0 := by
  simp [endpointFunction, selectedInverse_zero]

private lemma endpointFunction_real (y : ℝ) (hy : |y| < 7 / 2) :
    (endpointFunction y).im = 0 := by
  have hr : |y / 2| < 7 / 4 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hs := selectedInverse_real (y / 2) hr
  have hs' : (selectedInverse ((y : ℂ) / 2)).im = 0 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hs
  have he : selectedInverse ((y : ℂ) / 2) = ((selectedInverse ((y : ℂ) / 2)).re : ℂ) := by
    apply Complex.ext <;> simp [hs']
  dsimp [endpointFunction]
  rw [he]
  exact Complex.sin_ofReal_im _

private lemma endpointFunction_expansion :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ,
      HasFPowerSeriesOnBall endpointFunction p 0 (13 / 4) := by
  have hd : DifferentiableOn ℂ endpointFunction (closedBall 0 (13 / 4)) := by
    intro z hz
    exact (endpointFunction_analytic z (by
      have hz' : ‖z‖ ≤ 13 / 4 := by simpa using hz
      linarith)).differentiableAt.differentiableWithinAt
  refine ⟨cauchyPowerSeries endpointFunction 0 (13 / 4 : ℝ≥0), ?_⟩
  convert hd.hasFPowerSeriesOnBall (R := (13 / 4 : ℝ≥0)) (by norm_num) using 1
  norm_num

private lemma arcsine_hasSum (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ =>
      OriginalHalfBinomialIntegral.b n * x ^ (2 * n + 1) / (2 * n + 1))
      (Real.arcsin x) := by
  let b := OriginalHalfBinomialIntegral.b
  have ht (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : |t| ≤ |x| := by
    rcases (Set.mem_uIcc.mp ht) with ht | ht
    · rw [abs_of_nonneg (by linarith : 0 ≤ t), abs_of_nonneg (by linarith : 0 ≤ x)]
      exact ht.2
    · rw [abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonpos (by linarith : x ≤ 0)]
      linarith [ht.1]
  have hkernel : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
      MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div
      ((continuousOn_const.sub (continuousOn_id.pow 2)).sqrt)
    intro t ht'
    apply ne_of_gt (Real.sqrt_pos.mpr _)
    change 0 < 1 - t ^ 2
    exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (lt_of_le_of_lt (ht t ht') hx))
  have hi : (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 - t ^ 2)) = Real.arcsin x := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht' => Real.hasDerivAt_arcsin
        (by have := lt_of_le_of_lt (ht t ht') hx; intro he; simp [he] at this)
        (by have := lt_of_le_of_lt (ht t ht') hx; intro he; simp [he] at this))
      hkernel using 1
    simp
  have hsum : Summable (fun n : ℕ => |x| ^ (2 * n)) := by
    simpa [pow_mul] using summable_geometric_of_norm_lt_one
      (show ‖|x| ^ 2‖ < 1 by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (sq_lt_one_iff_abs_lt_one _).mpr (by simpa using hx))
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := MeasureTheory.volume) (a := 0) (b := x)
    (F := fun (n : ℕ) (t : ℝ) => b n * t ^ (2 * n))
    (f := fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2))
    (fun n (_ : ℝ) => |x| ^ (2 * n))
    (fun n => (continuous_const.mul (continuous_id.pow _)).aestronglyMeasurable)
    (fun n => MeasureTheory.ae_of_all _ fun t ht' => by
      have htx := ht t (Set.uIoc_subset_uIcc ht')
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (OriginalHalfBinomialIntegral.b_nonneg n),
        norm_pow, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (by positivity)
        (OriginalHalfBinomialIntegral.b_le_one n) |>.trans
          (pow_le_pow_left₀ (abs_nonneg _) htx _))
    (MeasureTheory.ae_of_all _ fun _ _ => hsum)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun t ht' => by
      have htx := lt_of_le_of_lt (ht t (Set.uIoc_subset_uIcc ht')) hx
      have ht2 : t ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr htx
      simpa [b, pow_mul] using
        OriginalHalfBinomialIntegral.binomial_hasSum (t ^ 2) (sq_nonneg t) ht2)
  rw [hi] at hs
  convert hs using 1
  ext n
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 2 * n + 1 ≠ 0), sub_zero,
    Nat.cast_mul, Nat.cast_ofNat]
  dsimp [b]
  ring

private lemma alpha_real_odd (n : ℕ) :
    (alpha (2 * n + 1) : ℝ) = OriginalHalfBinomialIntegral.b n / (2 * n + 1) := by
  simp only [alpha, show (2 * n + 1) / 2 = n by omega,
    show (2 * n + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte]
  push_cast
  dsimp [OriginalHalfBinomialIntegral.b, Nat.centralBinom]
  field_simp

private lemma alpha_real_bound (n : ℕ) : ‖(alpha n : ℝ)‖ ≤ 1 := by
  by_cases he : n % 2 = 0
  · simp [alpha, he]
  · obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    rw [hk, alpha_real_odd, Real.norm_eq_abs, abs_of_nonneg (by
      exact div_nonneg (OriginalHalfBinomialIntegral.b_nonneg k) (by positivity))]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * k + 1)).mpr
    have := OriginalHalfBinomialIntegral.b_le_one k
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

private lemma arcsine_expansion :
    HasFPowerSeriesAt Real.arcsin
      (PowerSeries.toFMS ℝ (arcsine.map (Rat.castHom ℝ))) 0 := by
  let p := PowerSeries.toFMS ℝ (arcsine.map (Rat.castHom ℝ))
  have hp : (1 : ℝ≥0∞) ≤ p.radius := by
    simpa using p.le_radius_of_bound 1 (r := 1) (fun n => by
      simpa [p, PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_norm,
        PowerSeries.coeff_map, arcsine] using alpha_real_bound n)
  refine ⟨1, hp, by norm_num, ?_⟩
  intro x hx
  have hx' : |x| < 1 := by
    simpa [edist_dist, dist_zero_right, Real.norm_eq_abs, ENNReal.ofReal_lt_one] using hx
  have hall : HasSum (fun n : ℕ => (alpha n : ℝ) * x ^ n) (0 + Real.arcsin x) := by
    apply HasSum.even_add_odd
    · simp [alpha]
    · convert arcsine_hasSum x hx' using 1
      ext n
      rw [alpha_real_odd]
      ring
  simpa [p, PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_apply_eq, arcsine,
    PowerSeries.coeff_map, smul_eq_mul, mul_comm] using hall

private lemma endpointFunction_inverse (y : ℝ) (hy : |y| < 7 / 2) :
    2 * (endpointFunction y).re + 2 * Real.arcsin (endpointFunction y).re = y := by
  have hr : |y / 2| < 7 / 4 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hs : (selectedInverse ((y : ℂ) / 2)).im = 0 := by
    simpa using selectedInverse_real (y / 2) hr
  let x := (selectedInverse ((y : ℂ) / 2)).re
  have he : selectedInverse ((y : ℂ) / 2) = (x : ℂ) := by
    apply Complex.ext <;> simp [x, hs]
  have hG := selectedInverse_spec ((y : ℂ) / 2) (by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    linarith)
  have hx : |x| < 1 := by simpa [he] using hG.1
  have hF : x + Real.sin x = y / 2 := by
    simpa [sineForward, he, Complex.sin_ofReal_re] using congrArg Complex.re hG.2
  have hH : (endpointFunction y).re = Real.sin x := by
    simp [endpointFunction, he, Complex.sin_ofReal_re]
  rw [hH, Real.arcsin_sin (by linarith [abs_le.mp hx.le, Real.pi_gt_three])
    (by linarith [le_abs_self x, Real.pi_gt_three])]
  linarith

private lemma forward_expansion :
    HasFPowerSeriesAt (fun x : ℝ => 2 * x + 2 * Real.arcsin x)
      (PowerSeries.toFMS ℝ (forward.map (Rat.castHom ℝ))) 0 := by
  have hX : PowerSeries.toFMS ℝ (PowerSeries.X : ℝ⟦X⟧) =
      (ContinuousLinearMap.id ℝ ℝ).fpowerSeries 0 := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    rcases n with _ | (_ | n)
    · simp [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars]
    · simp [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars]
    · simp [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars,
        PowerSeries.coeff_X]
  have hA : PowerSeries.toFMS ℝ (forward.map (Rat.castHom ℝ)) =
      (2 : ℝ) • PowerSeries.toFMS ℝ (PowerSeries.X : ℝ⟦X⟧) +
        (2 : ℝ) • PowerSeries.toFMS ℝ (arcsine.map (Rat.castHom ℝ)) := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    change PowerSeries.toFMS ℝ (forward.map (Rat.castHom ℝ)) n v =
      (2 : ℝ) * PowerSeries.toFMS ℝ (PowerSeries.X : ℝ⟦X⟧) n v +
        (2 : ℝ) * PowerSeries.toFMS ℝ (arcsine.map (Rat.castHom ℝ)) n v
    rw [PowerSeries.toFMS_apply, PowerSeries.toFMS_apply, PowerSeries.toFMS_apply]
    rw [PowerSeries.coeff_map]
    simp [forward, PowerSeries.coeff_X]
    split_ifs <;> norm_num <;> ring
  rw [hA, hX]
  convert ((ContinuousLinearMap.id ℝ ℝ).hasFPowerSeriesAt 0).const_smul
    (c := (2 : ℝ)) |>.add (arcsine_expansion.const_smul (c := (2 : ℝ))) using 1
  funext x
  rfl

private lemma inverse_coefficients (n : ℕ) :
    iteratedDeriv n endpointFunction 0 / (n.factorial : ℂ) =
      ((PowerSeries.coeff n inverse : ℚ) : ℂ) := by
  let h : ℝ → ℝ := fun y => (endpointFunction y).re
  have hH := endpointFunction_analytic 0 (by norm_num)
  have hreal : ∀ᶠ y : ℝ in 𝓝 0, (endpointFunction y).im = 0 := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
      (by norm_num : |(0 : ℝ)| < 7 / 2)] with y hy
    exact endpointFunction_real y hy
  obtain ⟨hh, hc⟩ :=
    D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis.real_taylor_data hH hreal
  let T : ℝ⟦X⟧ := PowerSeries.mk (fun k => iteratedDeriv k h 0 / k.factorial)
  let A := forward.map (Rat.castHom ℝ)
  have hT : HasFPowerSeriesAt h (PowerSeries.toFMS ℝ T) 0 := by
    simpa [T, PowerSeries.toFMS] using hh.hasFPowerSeriesAt
  have hT0 : T.constantCoeff = 0 := by simp [T, h, endpointFunction_zero]
  have hTs : PowerSeries.HasSubst T := PowerSeries.HasSubst.of_constantCoeff_zero' hT0
  have hA : HasFPowerSeriesAt (fun x : ℝ => 2 * x + 2 * Real.arcsin x)
      (PowerSeries.toFMS ℝ A) (h 0) := by
    simpa [h, endpointFunction_zero, A] using forward_expansion
  have he : (fun x : ℝ => 2 * h x + 2 * Real.arcsin (h x)) =ᶠ[𝓝 0] id := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
      (by norm_num : |(0 : ℝ)| < 7 / 2)] with y hy
    exact endpointFunction_inverse y hy
  have hcomp := (hA.comp hT).congr he
  have hEq := hcomp.eq_formalMultilinearSeries
    ((ContinuousLinearMap.id ℝ ℝ).hasFPowerSeriesAt 0)
  rw [← PowerSeries.toFMS_subst ℝ T A hTs] at hEq
  have hAT : A.subst T = PowerSeries.X := by
    ext k
    have hval := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ =>
      p k (fun _ => 1)) hEq
    rcases k with _ | (_ | k)
    · simpa [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_apply_eq] using hval
    · simpa [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_apply_eq] using hval
    · simpa [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_apply_eq,
        PowerSeries.coeff_X, show k + 1 + 1 ≠ 1 by omega] using hval
  have hA0 : A.constantCoeff = 0 := by
    change ((forward.constantCoeff : ℚ) : ℝ) = 0
    norm_num [forward, arcsine, alpha]
  have hu : IsUnit (PowerSeries.coeff 1 A) := by
    have hv : PowerSeries.coeff 1 A = 4 := by
      change ((PowerSeries.coeff 1 forward : ℚ) : ℝ) = 4
      norm_num [forward, arcsine, alpha]
    rw [hv]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  have hB : PowerSeries.HasSubst inverse := by
    dsimp [inverse]
    exact PowerSeries.HasSubst.substInvOfIsUnit _ _
  have hBi : forward.subst inverse = PowerSeries.X := by
    dsimp [inverse]
    exact PowerSeries.subst_substInvOfIsUnit_right _ (by simp [forward, arcsine, alpha]) _
  have hBM : A.subst (inverse.map (Rat.castHom ℝ)) = PowerSeries.X := by
    dsimp only [A]
    have hm := PowerSeries.map_subst (h := Rat.castHom ℝ) hB forward
    change (forward.subst inverse).map (Rat.castHom ℝ) =
      (forward.map (Rat.castHom ℝ)).subst (inverse.map (Rat.castHom ℝ)) at hm
    rw [← hm, hBi]
    change (PowerSeries.map (Rat.castHom ℝ)) PowerSeries.X = PowerSeries.X
    exact PowerSeries.map_X _
  have hBs : PowerSeries.HasSubst (inverse.map (Rat.castHom ℝ)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change ((inverse.constantCoeff : ℚ) : ℝ) = 0
      simp [inverse])
  have hTM : T = inverse.map (Rat.castHom ℝ) :=
    (PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X A hA0 hu hTs hAT).trans
      (PowerSeries.eq_substInvOfIsUnit_of_subst_eq_X A hA0 hu hBs hBM).symm
  have hn : iteratedDeriv n h 0 / n.factorial = ((PowerSeries.coeff n inverse : ℚ) : ℝ) := by
    simpa [T] using congrArg (PowerSeries.coeff n) hTM
  apply Complex.ext
  · simpa [h] using (hc n).2.trans hn
  · simpa using (hc n).1

private lemma endpoint_series :
    HasFPowerSeriesOnBall endpointFunction
      (PowerSeries.toFMS ℂ (inverse.map (Rat.castHom ℂ))) 0 (13 / 4) := by
  obtain ⟨p, hp⟩ := endpointFunction_expansion
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    ((endpointFunction_analytic 0 (by norm_num)).hasFPowerSeriesAt)
  have hc : p = PowerSeries.toFMS ℂ (inverse.map (Rat.castHom ℂ)) := by
    rw [he]
    congr 1
    funext n
    exact inverse_coefficients n
  rwa [← hc]

private lemma endpoint_value :
    0 < (endpointFunction Real.pi).re ∧ (endpointFunction Real.pi).re < 1 ∧
      Real.cos (endpointFunction Real.pi).re = (endpointFunction Real.pi).re := by
  let x := (selectedInverse ((Real.pi : ℂ) / 2)).re
  have hs : (selectedInverse ((Real.pi : ℂ) / 2)).im = 0 := by
    simpa using selectedInverse_real (Real.pi / 2) (by
      rw [abs_of_pos (half_pos Real.pi_pos)]
      linarith [Real.pi_lt_d2])
  have he : selectedInverse ((Real.pi : ℂ) / 2) = (x : ℂ) := by
    apply Complex.ext <;> simp [x, hs]
  have hG := selectedInverse_spec ((Real.pi : ℂ) / 2) (by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    linarith [Real.pi_lt_d2])
  have hx : |x| < 1 := by simpa [he] using hG.1
  have hF : x + Real.sin x = Real.pi / 2 := by
    simpa [sineForward, he, Complex.sin_ofReal_re] using congrArg Complex.re hG.2
  have hxpos : 0 < x := by
    by_contra hn
    have hsin := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hn)
      (by linarith [abs_le.mp hx.le, Real.pi_gt_three])
    linarith [Real.pi_pos]
  have hH : (endpointFunction Real.pi).re = Real.sin x := by
    simp [endpointFunction, he, Complex.sin_ofReal_re]
  rw [hH]
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hxpos (by
    linarith [le_abs_self x, Real.pi_gt_three]),
    lt_trans (Real.sin_lt hxpos) (lt_of_le_of_lt (le_abs_self x) hx), ?_⟩
  rw [show Real.sin x = Real.pi / 2 - x by linarith, Real.cos_pi_div_two_sub]
  linarith

private lemma positive_fixed_unique (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hfix : Real.cos θ = θ) (t : ℝ) (ht : 0 < t) (htfix : Real.cos t = t) :
    t = θ := by
  have ht1 : t ≤ 1 := htfix ▸ Real.cos_le_one t
  have htstrict : t < 1 := by
    have hcos := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      (show t ∈ Set.Icc 0 Real.pi from ⟨ht.le, by linarith [Real.pi_gt_three]⟩) ht
    simpa [htfix] using hcos
  have htpi : t ≤ Real.pi := htstrict.le.trans (by linarith [Real.pi_gt_three])
  have hanti := Real.antitoneOn_cos
  apply le_antisymm
  · by_contra hn
    have hle := hanti ⟨hθ.le, by linarith [Real.pi_gt_three]⟩
      ⟨ht.le, htpi⟩ (le_of_not_ge hn)
    rw [hfix, htfix] at hle
    linarith
  · by_contra hn
    have hle := hanti ⟨ht.le, htpi⟩
      ⟨hθ.le, by linarith [Real.pi_gt_three]⟩ (le_of_not_ge hn)
    rw [hfix, htfix] at hle
    linarith

/-- The literal rational inverse converges absolutely at pi to the unique positive
cosine fixed point. -/
theorem rational_inverse_endpoint :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ Real.cos θ = θ ∧
      (∀ t : ℝ, 0 < t → Real.cos t = t → t = θ) ∧
      Summable (fun n : ℕ => |((PowerSeries.coeff n inverse : ℚ) : ℝ)| * Real.pi ^ n) ∧
      HasSum (fun n : ℕ => ((PowerSeries.coeff n inverse : ℚ) : ℝ) * Real.pi ^ n) θ := by
  have hval := endpoint_value
  refine ⟨(endpointFunction Real.pi).re, hval.1, hval.2.1, hval.2.2,
    positive_fixed_unique _ hval.1 hval.2.1 hval.2.2, ?_, ?_⟩
  · let r : ℝ≥0 := ⟨Real.pi, Real.pi_pos.le⟩
    have hr : ENNReal.ofNNReal r <
        (PowerSeries.toFMS ℂ (inverse.map (Rat.castHom ℂ))).radius := by
      apply lt_of_lt_of_le (b := (13 / 4 : ℝ≥0∞)) _ endpoint_series.r_le
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal Real.pi < 13 / 4
      convert (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 13 / 4 by norm_num)).mpr
        (show Real.pi < 13 / 4 by linarith [Real.pi_lt_d2]) using 1 <;>
        norm_num [ENNReal.ofReal_div_of_pos]
    have hsum := (PowerSeries.toFMS ℂ (inverse.map (Rat.castHom ℂ))).summable_norm_mul_pow hr
    have hn (n : ℕ) :
        ‖PowerSeries.toFMS ℂ (inverse.map (Rat.castHom ℂ)) n‖ =
          |((PowerSeries.coeff n inverse : ℚ) : ℝ)| := by
      rw [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_norm,
        PowerSeries.coeff_map]
      change ‖((PowerSeries.coeff n inverse : ℚ) : ℂ)‖ = _
      rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    simp_rw [hn] at hsum
    exact hsum
  · have hsum := endpoint_series.hasSum_sub (y := (Real.pi : ℂ)) (by
      rw [Metric.mem_eball, edist_dist]
      simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      convert (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 13 / 4 by norm_num)).mpr
        (show Real.pi < 13 / 4 by linarith [Real.pi_lt_d2]) using 1 <;> norm_num [ENNReal.ofReal_div_of_pos])
    have hre := Complex.hasSum_re hsum
    simpa [PowerSeries.toFMS, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, ← Complex.ofReal_ratCast, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, mul_comm] using hre

end D5.S3.Analytic.PowerSeries.DottieInverseSeries
