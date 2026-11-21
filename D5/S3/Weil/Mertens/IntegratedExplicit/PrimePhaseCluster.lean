/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePhaseCluster
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual phase orbit closure gives the cluster values of normalized prime mass. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeAttainedShortWindows
import D5.S3.Weil.Mertens.IntegratedExplicit.RHPrimeWindowMean

/-! At a real-part upper bound above one half, the late prime-only windows
are approximated by a continuous integral on the actual zeta phase orbit closure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open MaximalRealPartProjection (maximalSeries)

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster

open PrimeAttainedShortWindows (normalized_complete_tail_approx normalized_prime_power_error)
open PrimeOnlyTailCorrection (primeTail prime_integrable)

/-- The simultaneous unit phases of all actual zero occurrences at real time `t`. -/
def phaseOrbit (t : ℝ) (k : ℕ) : Circle :=
  Circle.exp (t * (actualZero k).im)

/-- The complete-tail coefficient cut to the line with real part `β`. -/
def rightmostCoeff (realPart : ℂ → ℝ) (β : ℝ) (k : ℕ) : ℂ :=
  if realPart (actualZero k) = β then actualCoeff k else 0

/-- The real complete-tail profile at phase `h` and lag `u`. -/
def phaseProfile (realPart : ℂ → ℝ) (β : ℝ) (h : ℕ → Circle) (u : ℝ) : ℝ :=
  -(∑' k : ℕ, rightmostCoeff realPart β k * (h k : ℂ) * (phaseOrbit u k : ℂ)).re

/-- The normalized negative-part integral of the phase profile over a log window. -/
def phaseWindow (realPart : ℂ → ℝ) (β W : ℝ) (h : ℕ → Circle) : ℝ :=
  ∫ s in 0..W, Real.exp (-(β - 1 / 2) * s) * max (-phaseProfile realPart β h (-s)) 0

private theorem phaseOrbit_add (t u : ℝ) : phaseOrbit (t + u) = phaseOrbit t * phaseOrbit u := by
  funext k
  simp only [phaseOrbit, Pi.mul_apply, add_mul, Circle.exp_add]

private theorem phaseOrbit_nat (n : ℕ) : phaseOrbit (n : ℝ) = phaseOrbit 1 ^ n := by
  funext k
  simp only [phaseOrbit, Pi.pow_apply, one_mul, Circle.exp_natCast_mul]

theorem phaseOrbit_cluster_iff (h : ℕ → Circle) :
    MapClusterPt h atTop phaseOrbit ↔ h ∈ closure (range phaseOrbit) := by
  constructor
  · intro hc
    exact isClosed_closure.mem_of_mapClusterPt hc
      (Eventually.of_forall fun t => subset_closure (mem_range_self t))
  · intro hh
    refine closure_minimal (t := {p | MapClusterPt p atTop phaseOrbit}) ?_
      isClosed_setOfPred_clusterPt hh
    rintro _ ⟨t, rfl⟩
    have hmul : Continuous (fun v : ℕ → Circle => phaseOrbit t * v) :=
      continuous_const.mul continuous_id
    have hrec := (mapClusterPt_one_atTop_pow (phaseOrbit 1)).continuousAt_comp hmul.continuousAt
    have hcofinal : Tendsto (fun n : ℕ => t + (n : ℝ)) atTop atTop :=
      tendsto_atTop.2 fun c => (tendsto_natCast_atTop_atTop.eventually_ge_atTop (c - t)).mono
        fun _ hn => by linarith only [hn]
    apply MapClusterPt.of_comp hcofinal
    simpa only [mul_one, Function.comp_def, phaseOrbit_add, phaseOrbit_nat] using hrec

theorem phaseProfile_continuous (realPart : ℂ → ℝ) (β : ℝ) :
    Continuous (fun q : (ℕ → Circle) × ℝ => phaseProfile realPart β q.1 q.2) := by
  apply Continuous.neg
  apply Complex.continuous_re.comp
  apply continuous_tsum (fun k => by unfold phaseOrbit; fun_prop)
    actualCoeff_hasSum.summable.norm
  intro k q
  simp only [norm_mul, Circle.norm_coe, mul_one, rightmostCoeff]
  split_ifs
  · rfl
  · simpa only [norm_zero] using norm_nonneg (actualCoeff k)

theorem phaseWindow_continuous (β W : ℝ) : Continuous (phaseWindow Complex.re β W) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (continuous_exp_weight β |>.mul
      (((phaseProfile_continuous Complex.re β).comp
        (continuous_fst.prodMk continuous_snd.neg)).neg.max continuous_const)) 0 W
where
  continuous_exp_weight (β : ℝ) :
      Continuous (fun q : (ℕ → Circle) × ℝ => Real.exp (-(β - 1 / 2) * q.2)) := by
    fun_prop

theorem phaseProfile_on_orbit (β t u : ℝ) :
    phaseProfile Complex.re β (phaseOrbit t) u =
      -(maximalSeries actualCoeff actualZero β (t + u)).re := by
  unfold phaseProfile maximalSeries
  congr 2
  apply tsum_congr
  intro k
  change rightmostCoeff Complex.re β k * (phaseOrbit t k : ℂ) * (phaseOrbit u k : ℂ) =
    if (actualZero k).re = β then
      actualCoeff k * Complex.exp (((t + u : ℝ) : ℂ) * (actualZero k - (β : ℂ))) else 0
  unfold rightmostCoeff
  split_ifs with hk
  · rw [mul_assoc, ← Circle.coe_mul, ← Pi.mul_apply, ← phaseOrbit_add, phaseOrbit, Circle.coe_exp]
    congr 2
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, hk]
  · simp

def signedInput (β u : ℝ) : ℝ :=
  Real.exp ((1 - β) * u) * primeTail (Real.exp u)

theorem signedInput_approx {β : ℝ} (hβ₀ : 0 < β) (hβ : 1 / 2 < β)
    (hmax : ∀ k, (actualZero k).re ≤ β) :
    Tendsto (fun u : ℝ => signedInput β u +
      (maximalSeries actualCoeff actualZero β u).re) atTop (𝓝 0) := by
  have h := (normalized_complete_tail_approx hβ₀ hmax).sub (normalized_prime_power_error hβ)
  rw [sub_self] at h
  refine h.congr' (Eventually.of_forall fun u => ?_)
  unfold signedInput
  ring

theorem primeMass_exp_substitution (β W t : ℝ) (hW : 0 ≤ W) (ht : W ≤ t) :
    (∫ x in Real.exp t * Real.exp (-W)..Real.exp t, max (-primeTail x) 0 / Real.sqrt x) /
      (Real.exp t) ^ (β - 1 / 2) =
    ∫ s in 0..W, Real.exp (-(β - 1 / 2) * s) * max (-signedInput β (t - s)) 0 := by
  let density (x : ℝ) := max (-primeTail x) 0 / Real.sqrt x
  have hdensity : ContinuousOn density (Ici 1) := by
    have hprime : ContinuousOn primeTail (Ici 1) :=
      prime_integrable.continuousOn_Ici_primitive_Ioi
    exact (hprime.neg.sup continuousOn_const).div
      Real.continuous_sqrt.continuousOn
      (fun x hx => (Real.sqrt_pos.mpr (zero_lt_one.trans_le (mem_Ici.mp hx))).ne')
  have hchange := intervalIntegral.integral_comp_mul_deriv'
    (a := t - W) (b := t) (f := Real.exp) (f' := Real.exp) (g := density)
    (fun u _ => Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn (hdensity.mono (by
      rintro _ ⟨u, hu, rfl⟩
      rw [uIcc_of_le (sub_le_self t hW)] at hu
      exact Real.one_le_exp ((sub_nonneg.mpr ht).trans hu.1)))
  have hreflect := intervalIntegral.integral_comp_sub_left
    (a := 0) (b := W) (fun u => density (Real.exp u) * Real.exp u) t
  rw [sub_zero] at hreflect
  change (∫ x in Real.exp t * Real.exp (-W)..Real.exp t, density x) /
    (Real.exp t) ^ (β - 1 / 2) = _
  rw [← Real.exp_add, ← sub_eq_add_neg, ← hchange]
  simp only [Function.comp_def]
  rw [← hreflect, div_eq_mul_inv, mul_comm _ (_⁻¹), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  unfold density signedInput
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_neg,
    show -(Real.exp ((1 - β) * (t - s)) * primeTail (Real.exp (t - s))) =
      Real.exp ((1 - β) * (t - s)) * (-primeTail (Real.exp (t - s))) by rw [mul_neg],
    show max (Real.exp ((1 - β) * (t - s)) * -primeTail (Real.exp (t - s))) 0 =
      Real.exp ((1 - β) * (t - s)) * max (-primeTail (Real.exp (t - s))) 0 by
        rw [mul_max_of_nonneg _ _ (Real.exp_nonneg _), mul_zero],
    div_eq_mul_inv (max (-primeTail (Real.exp (t - s))) 0), ← Real.exp_neg]
  generalize max (-primeTail (Real.exp (t - s))) 0 = m
  calc
    _ = Real.exp (-(t * (β - 1 / 2)) + (-((t - s) * (1 / 2)) + (t - s))) * m := by
      simp only [Real.exp_add]
      ring
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- An arbitrarily small tail error bounds every late window by the same integrated weight. -/
theorem window_transfer {β W : ℝ} (hW : 0 ≤ W)
    (happrox : Tendsto (fun u : ℝ => signedInput β u +
      (maximalSeries actualCoeff actualZero β u).re) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ =>
      (∫ x in Real.exp t * Real.exp (-W)..Real.exp t, max (-primeTail x) 0 / Real.sqrt x) /
        (Real.exp t) ^ (β - 1 / 2) - phaseWindow Complex.re β W (phaseOrbit t)) atTop (𝓝 0) := by
  let weight (s : ℝ) := Real.exp (-(β - 1 / 2) * s)
  let K := ∫ s in 0..W, weight s
  have hcweight : Continuous weight := by unfold weight; fun_prop
  have hK : 0 ≤ K := intervalIntegral.integral_nonneg hW fun s _ => Real.exp_nonneg _
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let δ := ε / (K + 1)
  have hK₁ : 0 < K + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hK₁
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp happrox) δ hδ)
  filter_upwards [eventually_ge_atTop W, eventually_ge_atTop (T + W)] with t ht htT
  rw [primeMass_exp_substitution β W t hW ht, Real.dist_eq, sub_zero]
  let a (s : ℝ) := weight s * max (-signedInput β (t - s)) 0
  let b (s : ℝ) := weight s * max (-phaseProfile Complex.re β (phaseOrbit t) (-s)) 0
  have ha : IntervalIntegrable a volume 0 W := by
    apply ContinuousOn.intervalIntegrable_of_Icc hW
    refine hcweight.continuousOn.mul ((ContinuousOn.neg ?_).sup continuousOn_const)
    unfold signedInput
    refine (by fun_prop : Continuous fun s : ℝ => Real.exp ((1 - β) * (t - s))).continuousOn.mul
      (prime_integrable.continuousOn_Ici_primitive_Ioi.comp
        (by fun_prop : Continuous fun s : ℝ => Real.exp (t - s)).continuousOn ?_)
    intro s hs
    exact Real.one_le_exp (sub_nonneg.mpr (hs.2.trans ht))
  have hb : IntervalIntegrable b volume 0 W := by
    apply Continuous.intervalIntegrable
    exact hcweight.mul
      (((phaseProfile_continuous Complex.re β).comp
        (continuous_const.prodMk continuous_neg)).neg.max continuous_const)
  have hab (s : ℝ) (hs : s ∈ Icc 0 W) : |a s - b s| ≤ δ * weight s := by
    have hsmall := hT (t - s) (by linarith only [hs.2, htT])
    rw [Real.dist_eq, sub_zero] at hsmall
    have hlip := abs_max_sub_max_le_max (-signedInput β (t - s)) 0
      (-phaseProfile Complex.re β (phaseOrbit t) (-s)) 0
    have hprofile := phaseProfile_on_orbit β t (-s)
    rw [← sub_eq_add_neg] at hprofile
    have hdiff : |-signedInput β (t - s) - -phaseProfile Complex.re β (phaseOrbit t) (-s)| =
        |signedInput β (t - s) + (maximalSeries actualCoeff actualZero β (t - s)).re| := by
      rw [← neg_sub, abs_neg, hprofile, sub_neg_eq_add]
      congr 1
      ring
    simp only [hdiff, sub_self, abs_zero,
      max_eq_left (abs_nonneg (signedInput β (t - s) +
        (maximalSeries actualCoeff actualZero β (t - s)).re))] at hlip
    change |weight s * max (-signedInput β (t - s)) 0 -
      weight s * max (-phaseProfile Complex.re β (phaseOrbit t) (-s)) 0| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.exp_nonneg _), mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hlip.trans hsmall.le) (Real.exp_nonneg _)
  change |(∫ s in 0..W, a s) - ∫ s in 0..W, b s| < ε
  rw [← intervalIntegral.integral_sub ha hb]
  calc
    _ ≤ ∫ s in 0..W, |a s - b s| := intervalIntegral.abs_integral_le_integral_abs hW
    _ ≤ ∫ s in 0..W, δ * weight s :=
      intervalIntegral.integral_mono_on hW (ha.sub hb).abs
        ((hcweight.const_mul δ).intervalIntegrable _ _) hab
    _ = δ * K := intervalIntegral.integral_const_mul δ weight
    _ < ε := by
      calc
        δ * K < δ * (K + 1) := mul_lt_mul_of_pos_left (lt_add_one K) hδ
        _ = ε := div_mul_cancel₀ _ hK₁.ne'

theorem mapClusterPt_of_sub_tendsto_zero {f g : ℝ → ℝ} {y : ℝ}
    (hfg : Tendsto (fun t => f t - g t) atTop (𝓝 0))
    (hf : MapClusterPt y atTop f) : MapClusterPt y atTop g := by
  refine (Metric.nhds_basis_ball.mapClusterPt_iff_frequently.mp hf |> fun h =>
    Metric.nhds_basis_ball.mapClusterPt_iff_frequently.mpr fun ε hε => ?_)
  have he := (Metric.tendsto_nhds.mp hfg) (ε / 2) (half_pos hε)
  refine ((h (ε / 2) (half_pos hε)).and_eventually he).mono fun t ⟨ht, hdiff⟩ => ?_
  rw [Metric.mem_ball] at ht ⊢
  rw [Real.dist_eq, sub_zero, abs_sub_comm] at hdiff
  exact (dist_triangle (g t) (f t) y).trans_lt
    (by rw [Real.dist_eq (g t) (f t)]; linarith only [ht, hdiff])

/-- At any real-part upper bound above one half and any fixed nonnegative logarithmic
width, the normalized actual prime-only mass has precisely the cluster values supplied
by the actual phase orbit closure with coefficients cut to the upper-bound line. -/
theorem prime_tail_mass_cluster_iff_of_upper_bound (β : ℝ) :
    let realPart := Complex.re
    1 / 2 < β → (∀ z : ℂ, IsNontrivialZero z → realPart z ≤ β) →
    ∀ (W : ℝ), 0 ≤ W → ∀ (y : ℝ),
    MapClusterPt y atTop (fun B : ℝ =>
      (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) /
        B ^ (β - 1 / 2)) ↔
    ∃ h ∈ closure (range phaseOrbit), y = phaseWindow realPart β W h := by
  dsimp only
  intro hβ hmax W hW y
  let mass (B : ℝ) :=
    (∫ x in B * Real.exp (-W)..B, max (-primeTail x) 0 / Real.sqrt x) / B ^ (β - 1 / 2)
  let window := phaseWindow Complex.re β W
  have happrox := window_transfer hW (signedInput_approx (by linarith only [hβ]) hβ
    (fun k => hmax _ (actualData.zero_isNontrivial (actualOccurrenceEquiv k).1)))
  change Tendsto (fun t => (mass ∘ Real.exp) t - (window ∘ phaseOrbit) t) atTop (𝓝 0) at happrox
  have hlog : MapClusterPt y atTop mass ↔ MapClusterPt y atTop (mass ∘ Real.exp) := by
    constructor
    · intro h
      apply MapClusterPt.of_comp Real.tendsto_log_atTop
      apply h.congrFun
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with B hB
      exact (congrArg mass (Real.exp_log hB)).symm
    · exact MapClusterPt.of_comp Real.tendsto_exp_atTop
  change MapClusterPt y atTop mass ↔ _
  rw [hlog]
  have himage : IsClosed (window '' closure (range phaseOrbit)) :=
    ((isClosed_closure.isCompact).image (phaseWindow_continuous β W)).isClosed
  constructor
  · intro hy
    have hm := himage.mem_of_mapClusterPt (mapClusterPt_of_sub_tendsto_zero happrox hy)
      (Eventually.of_forall fun t => mem_image_of_mem window (subset_closure (mem_range_self t)))
    obtain ⟨h, hh, hval⟩ := hm
    exact ⟨h, hh, hval.symm⟩
  · rintro ⟨h, hh, rfl⟩
    have hc := ((phaseOrbit_cluster_iff h).mpr hh).continuousAt_comp
      (phaseWindow_continuous β W).continuousAt
    exact mapClusterPt_of_sub_tendsto_zero
      (by simpa only [neg_sub, neg_zero] using happrox.neg) hc

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePhaseCluster
