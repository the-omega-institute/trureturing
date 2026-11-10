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
import D5.S3.Analytic.OriginalHalfBinomialIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import D5.S3.Analytic.PowerSeries.ScalarComposition
import D5.S3.Analytic.Fourier.PositiveDefiniteImaginaryAxis

/-! The literal rational coefficients and compositional inverse. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Metric
open scoped Topology PowerSeries

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
    dsimp only [inverseStep]
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
  have hyfix : inverseStep (sineForward x) y = y := by rw [he]; dsimp [inverseStep, sineForward]; ring
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
  have hd := sineForward_deriv_ne_zero x (mem_closedBall.mpr
    (le_of_lt (mem_ball.mp hx.1)))
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
  exact Complex.analyticAt_sin.comp
    ((selectedInverse_analytic (y / 2) hr).comp (analyticAt_id.div_const 2))

private lemma endpointFunction_zero : endpointFunction 0 = 0 := by
  simp [endpointFunction, selectedInverse_zero]

private lemma endpointFunction_real (y : ℝ) (hy : |y| < 7 / 2) :
    (endpointFunction y).im = 0 := by
  have hr : |y / 2| < 7 / 4 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hs := selectedInverse_real (y / 2) hr
  have he : selectedInverse ((y : ℂ) / 2) = ((selectedInverse ((y : ℂ) / 2)).re : ℂ) := by
    apply Complex.ext <;> simp [← Complex.ofReal_div, hs]
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
  exact ⟨_, hd.hasFPowerSeriesOnBall (R := (13 / 4 : ℝ≥0)) (by norm_num)⟩

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
    have := lt_of_le_of_lt (ht t ht') hx
    nlinarith [sq_abs t]
  have hi : (∫ t in (0 : ℝ)..x, 1 / Real.sqrt (1 - t ^ 2)) = Real.arcsin x := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht' => Real.hasDerivAt_arcsin
        (by have := lt_of_le_of_lt (ht t ht') hx; intro he; simp [he] at this)
        (by have := lt_of_le_of_lt (ht t ht') hx; intro he; simp [he] at this))
      hkernel using 1
    simp
  have hsum : Summable (fun n : ℕ => |x| ^ (2 * n)) := by
    simpa [pow_mul] using summable_geometric_of_norm_lt_one
      (show ‖|x| ^ 2‖ < 1 by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith)
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
      have ht2 : t ^ 2 < 1 := by nlinarith [sq_abs t]
      simpa [b, pow_mul] using
        OriginalHalfBinomialIntegral.binomial_hasSum (t ^ 2) (sq_nonneg t) ht2)
  rw [hi] at hs
  convert hs using 1
  ext n
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp

end D5.S3.Analytic.PowerSeries.DottieInverseSeries

