/- GID: D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An attained maximal zeta zero gives the Robin lower-bound criterion on ratio-one meshes. -/

import Mathlib.MeasureTheory.Function.Floor
import D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer
import D5.S3.Analytic.Asymptotics.CanonicalThresholdWindowTransfer
import D5.S3.Analytic.Laplace.MaximalRealPartProjection
import D5.S3.Arith.Robin.ActualTwoPriceDefect
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
import D5.S3.Arith.Robin.Analytic.ActualUnattainedThetaWindows
import D5.S3.Arith.Robin.PriceRecord.ActualRecordAllLogBudgetRemainder
import D5.S3.Arith.Robin.PriceRecord.RHSharpOriginalRecordMargin
import D5.S3.Arith.Robin.ThetaTailRobinWitness
import D5.S3.Weil.Mertens.CriticalThetaTailPeak
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-!
# Canonical Robin records on meshes with vanishing logarithmic gaps

An attained maximal abscissa in the right half of the critical strip gives
fixed positive excursions of the real maximal-line series. The actual
theta-tail peak and the signed arithmetic asymptotic supply these excursions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap

open D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer
open MaximalRealPartProjection
open D5.S3.Weil.ZeroSum (IsNontrivialZero)
open D5.S3.Weil.Mertens.IntegratedExplicit
  (actualCoeff actualCoeff_hasSum actualH actual_complete_H_package)
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction (golden_right_half_strip_implies_rh)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
  (actualZero actualData actualOccurrenceEquiv)
open D5.S3.Weil.GronwallLowerEnvelope (robinLogMargin)
open D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
  (B D finite_cancellation actual_B_rh_signed_asymptotic)
open D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
open D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature (loglog_tangent_gap_quadratic)
open D5.S3.Arith.Robin.ThetaTailRobinWitness (theta_tail_mertens_robin)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualTwoPriceDefect (strictInteger strictInteger_spec strict_layer_iff)
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open ActualBalancedCutoff (firstLayerPrice)
open RHSharpOriginalRecordMargin (Pn)

private theorem actual_normalized_B_add_maximal_tendsto {Θ : ℝ} (hΘ : 1 / 2 < Θ)
    (hΘone : Θ < 1) (hstrip : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ Θ) :
    Tendsto (fun u : ℝ => Real.exp ((1 - Θ) * u) * u * B (Real.exp u) +
      (maximalSeries actualCoeff actualZero Θ u).re) atTop (𝓝 0) := by
  have hstrip' : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ 1 - (1 - Θ) := by
    simpa only [sub_sub_cancel] using hstrip
  have hB := actual_B_critical_strip_signed_asymptotic (1 - Θ)
    (sub_pos.mpr hΘone) (by linarith only [hΘ]) hstrip'
  rw [sub_sub_cancel] at hB
  have hproj := tendsto_exp_mul_tsum_sub_maximalSeries
    (z := actualZero) (Θ := Θ) actualCoeff_hasSum.summable.norm
    (fun n => hstrip (actualZero n) (actualData.zero_isNontrivial (actualOccurrenceEquiv n).1))
  have hre : Tendsto (fun u : ℝ => Real.exp (-Θ * u) * (actualH u).re -
      (maximalSeries actualCoeff actualZero Θ u).re) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.sub_re, Complex.re_ofReal_mul, Complex.zero_re,
      actualH] using (Complex.continuous_re.tendsto (0 : ℂ)).comp hproj
  have hdiff := hB.sub hre
  rw [sub_self] at hdiff
  exact hdiff.congr (fun u => by ring)

private theorem eventually_B_le_theta_tail : ∀ᶠ x : ℝ in atTop,
    B x ≤ -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x + 4 / x := by
  have hp := EulerLayerRootCorrection.prime_number_limits.2.eventually
    (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hp, eventually_gt_atTop (4 : ℝ)] with x hratio hx
  have hx0 : 0 < x := by linarith only [hx]
  have hθ : 2 < Chebyshev.theta x := by
    have h := (lt_div_iff₀ hx0).mp hratio
    linarith only [h, hx]
  have hx1 : 1 < x := by linarith only [hx]
  have hθ1 : 1 < Chebyshev.theta x := by linarith only [hθ]
  have hcurve := (loglog_tangent_gap_quadratic hx1 hθ1).1
  let t := max x (Chebyshev.theta x)
  have hlogt := (Real.log_pos (hx1.trans_le (le_max_left x (Chebyshev.theta x)))).le
  have hnonneg : 0 ≤ (1 + Real.log t) / (t ^ 2 * (Real.log t) ^ 2) *
      (Chebyshev.theta x - x) ^ 2 / 2 :=
    div_nonneg (mul_nonneg
      (div_nonneg (by linarith only [hlogt]) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (sq_nonneg _)) (by norm_num)
  have htangent : 0 ≤ Real.log (Real.log x) + (Chebyshev.theta x - x) / (x * Real.log x) -
      Real.log (Real.log (Chebyshev.theta x)) := hnonneg.trans hcurve
  have htail := (theta_tail_mertens_robin x (by linarith only [hx])).2.1
  change D5.S3.Weil.Mertens.ActualThetaTailLaplace.F x =
    Mertens.E₂p x - (Chebyshev.theta x - x) / (x * Real.log x) at htail
  have hf : Mertens.E₃ x + Mertens.E₂p x ≤ 4 / x :=
    (le_abs_self _).trans (finite_cancellation (by linarith only [hx]))
  unfold B
  linarith only [htangent, htail, hf]

/-- Each natural index is a literal actual zero occurrence. The peak supplier
uses the analytic multiplicity of the attained zero in its coefficient. -/
private theorem actual_maximal_series_positive_peaks {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hρhalf : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, ∃ u : ℝ, T ≤ u ∧
      3 * c ≤ (maximalSeries actualCoeff actualZero ρ.re u).re := by
  have hz : riemannZeta ρ = 0 := by
    simpa only [D5.S3.Weil.Convention.classicalZeta] using hρ.1
  have hρone := hρ.2.2
  have hρ₀ : ρ ≠ 0 := by
    intro he
    have h := hρ.2.1
    simpa [he] using h
  have hρ₁ : ρ ≠ 1 := by
    intro he
    simpa [he] using hρone
  have hden : 0 < ‖ρ‖ * ‖ρ - 1‖ :=
    mul_pos (norm_pos_iff.mpr hρ₀) (norm_pos_iff.mpr (sub_ne_zero.mpr hρ₁))
  obtain ⟨hm, _, hpeaks⟩ :=
    D5.S3.Weil.Mertens.CriticalThetaTailPeak.critical_theta_tail_peak hρhalf hρone hz
  let A : ℝ := (analyticOrderNatAt riemannZeta ρ : ℝ) / (‖ρ‖ * ‖ρ - 1‖)
  have hA : 0 < A := div_pos (by exact_mod_cast hm) hden
  let c := A / 8
  have hc : 0 < c := by dsimp [c]; linarith only [hA]
  have hcoef : 5 * c < A := by dsimp [c]; linarith only [hA]
  have herror := actual_normalized_B_add_maximal_tendsto hρhalf hρone hmax
  have hsmall : Tendsto (fun u : ℝ => 4 * u * Real.exp (-ρ.re * u)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 : ℝ) ρ.re hρ.2.1).const_mul (4 : ℝ)
    simpa only [Real.rpow_one, mul_zero, mul_assoc] using hh
  have hupper : ∀ᶠ u : ℝ in atTop,
      Real.exp ((1 - ρ.re) * u) * u * B (Real.exp u) ≤
        -(u * Real.exp ((1 - ρ.re) * u) * D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u) +
          4 * u * Real.exp (-ρ.re * u) := by
    filter_upwards [Real.tendsto_exp_atTop.eventually eventually_B_le_theta_tail,
      eventually_ge_atTop (0 : ℝ)] with u hu hu₀
    change B (Real.exp u) ≤ -D5.S3.Weil.Mertens.ActualThetaTailLaplace.F (Real.exp u) +
      4 / Real.exp u at hu
    rw [← D5.S3.Weil.Mertens.ActualThetaTailLaplace.tail_substitution u] at hu
    have hscale : 0 ≤ Real.exp ((1 - ρ.re) * u) * u := mul_nonneg (Real.exp_pos _).le hu₀
    have hmul := mul_le_mul_of_nonneg_left hu hscale
    have hexp : Real.exp ((1 - ρ.re) * u) / Real.exp u = Real.exp (-ρ.re * u) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    calc
      _ ≤ Real.exp ((1 - ρ.re) * u) * u *
          (-D5.S3.Weil.Mertens.ActualThetaTailLaplace.f u + 4 / Real.exp u) := hmul
      _ = _ := by rw [← hexp]; ring
  obtain ⟨U, hU⟩ := eventually_atTop.mp (hupper.and
    ((hsmall.eventually (gt_mem_nhds hc)).and
      (herror.eventually (lt_mem_nhds (neg_lt_zero.mpr hc)))))
  refine ⟨c, hc, fun T => ?_⟩
  obtain ⟨u, hu, hp⟩ := hpeaks (5 * c) (mul_nonneg (by norm_num) hc.le) hcoef (max T U)
  have hlu : max T U ≤ u := ((le_max_left _ _).trans hu.le)
  obtain ⟨hup, hs, he⟩ := hU u ((le_max_right _ _).trans hlu)
  exact ⟨u, (le_max_left _ _).trans hlu, by linarith only [hp, hup, hs, he]⟩

/-- The actual arithmetic `B` has fixed negative normalized excursions along
every real log-coordinate mesh whose forward gaps tend to zero. -/
theorem actual_B_negative_on_vanishing_gap_mesh {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hρhalf : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re)
    {y : ℕ → ℝ} (hy : Tendsto y atTop atTop)
    (hgap : Tendsto (fun k => y (k + 1) - y k) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      Real.exp ((1 - ρ.re) * y k) * y k * B (Real.exp (y k)) < -c := by
  obtain ⟨c, hc, hpeaks⟩ := actual_maximal_series_positive_peaks hρ hρhalf hmax
  have huc : UniformContinuous (fun u => (maximalSeries actualCoeff actualZero ρ.re u).re) :=
    Complex.uniformContinuous_re.comp
      (uniformContinuous_maximalSeries actualCoeff_hasSum.summable.norm)
  have happrox := (actual_normalized_B_add_maximal_tendsto hρhalf hρ.2.2 hmax).comp hy
  exact ⟨c, hc, arbitrarily_late_negative_samples huc hy hgap happrox hc hpeaks⟩

private abbrev canonicalRecord (N : ℕ) : ℕ := strictInteger (firstLayerPrice ((N : ℝ) + 1))

private abbrev weight (a x : ℝ) : ℝ := Real.rpow x a * Real.log x

-- The support argument of PolynomialCanonicalRecordCriterion.specified_data,
-- specialized to the literal strictInteger at the prescribed price.
private lemma canonical_record_data {N : ℕ} (hN : 2 ≤ N) :
    0 < firstLayerPrice ((N : ℝ) + 1) ∧ 2 ≤ canonicalRecord N ∧
    (∀ n : ℕ, 0 < n → n < canonicalRecord N →
      goldenResourceObjective (firstLayerPrice ((N : ℝ) + 1)) n <
        goldenResourceObjective (firstLayerPrice ((N : ℝ) + 1)) (canonicalRecord N)) ∧
    largestPrime (canonicalRecord N) = Pn (N : ℝ) := by
  let q := firstLayerPrice ((N : ℝ) + 1)
  let m := canonicalRecord N
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : 1 < (N : ℝ) + 1 := by linarith only [hNreal]
  have hq : 0 < q := by
    change 0 < Real.log (1 + 1 / ((N : ℝ) + 1)) / Real.log ((N : ℝ) + 1)
    have hinv : 0 < 1 / ((N : ℝ) + 1) := one_div_pos.mpr (by linarith only [hN1])
    exact div_pos (Real.log_pos (by linarith only [hinv])) (Real.log_pos hN1)
  have hactive (p : ℕ) (hp : p.Prime) :
      q < goldenLayerMarginal p 1 ↔ p ≤ N := by
    rw [golden_layer_marginal_one_eq_log_one_add_inv hp]
    change firstLayerPrice ((N : ℝ) + 1) < firstLayerPrice (p : ℝ) ↔ p ≤ N
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    constructor
    · intro h
      by_contra hnot
      have hle : (N : ℝ) + 1 ≤ p := by exact_mod_cast (show N + 1 ≤ p by omega)
      exact (not_lt_of_ge (ActualBalancedCutoff.firstLayerPrice_strictAnti.antitoneOn
        hN1 hp1 hle)) h
    · intro hpN
      have hpNr : (p : ℝ) ≤ N := by exact_mod_cast hpN
      exact ActualBalancedCutoff.firstLayerPrice_strictAnti hp1 hN1 (by linarith only [hpNr])
  obtain ⟨hm, _, hopt, hleast⟩ := strictInteger_spec hq
  change 1 ≤ m at hm
  have hm₀ : m ≠ 0 := by omega
  have hdvd (p : ℕ) (hp : p.Prime) : p ∣ m ↔ p ≤ N :=
    (hp.dvd_iff_one_le_factorization hm₀).trans
      ((strict_layer_iff hq hp (by norm_num : 1 ≤ (1 : ℕ))).trans (hactive p hp))
  have hs : m.primeFactors = Nat.primesLE N := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp', hpdiv, _⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primesLE.mpr ⟨(hdvd p hp').mp hpdiv, hp'⟩
    · intro hp
      obtain ⟨hpN, hp'⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hp', (hdvd p hp').mpr hpN, hm₀⟩
  have hm2 : 2 ≤ m := Nat.le_of_dvd (by omega) ((hdvd 2 Nat.prime_two).mpr hN)
  have hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective q n < goldenResourceObjective q m := by
    intro n hn hnm
    have hle := hopt n (by omega)
    by_contra! hnot
    have heq := le_antisymm hle hnot
    have hnopt : IsGoldenResourceOptimal q n := by
      intro j hj
      rw [heq]
      exact hopt j hj
    exact (Nat.le_of_dvd hn (hleast n (by omega) hnopt)).not_gt hnm
  refine ⟨hq, hm2, hrecord, ?_⟩
  change largestPrime m = Pn (N : ℝ)
  simp only [largestPrime, Pn, Nat.floor_natCast, hs]

private lemma canonical_root_correction_tendsto {N : ℕ → ℕ}
    (hx : Tendsto (fun k => (N k : ℝ)) atTop atTop) :
    Tendsto (fun k => D (N k : ℝ) *
      (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ))) atTop
      (𝓝 (2 * Real.sqrt 2)) := by
  have hPn := RHSharpOriginalRecordMargin.Pn_atTop.comp hx
  have hscaled : Tendsto (fun k => D (Pn (N k : ℝ) : ℝ) *
      (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ))) atTop
      (𝓝 (2 * Real.sqrt 2)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨T, _, hlead⟩ := RHSharpOriginalRecordMargin.fullC_leading ε hε
    filter_upwards [hx.eventually_ge_atTop (2 : ℝ), hPn.eventually_ge_atTop T] with k hk hPk
    have hNk : 2 ≤ N k := by exact_mod_cast hk
    obtain ⟨hq, hm, hrecord, hprime⟩ := canonical_record_data hNk
    have hlarge : T ≤ (largestPrime (canonicalRecord (N k)) : ℝ) := by
      simpa only [Function.comp_def, hprime] using hPk
    have hmargin : robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ) =
        FullArithmeticCorrectionSecondOrder.correction (canonicalRecord (N k)) := by
      rw [RHSharpOriginalRecordMargin.margin_identity hm hq hrecord, hprime,
        RHSharpOriginalRecordMargin.B_prefix, add_sub_cancel_left]
    rw [Real.dist_eq, hmargin]
    simpa only [hprime] using (hlead _ hm _ hq hrecord hlarge).2.2
  have h := hscaled.div (RHSharpOriginalRecordMargin.normalization.comp hx)
    (one_ne_zero : (1 : ℝ) ≠ 0)
  rw [div_one] at h
  apply h.congr'
  filter_upwards [hPn.eventually_gt_atTop (1 : ℝ)] with k hPk
  let x : ℝ := N k
  let P : ℝ := Pn x
  let Δ : ℝ := robinLogMargin (canonicalRecord (N k)) - B x
  change 1 < P at hPk
  have hDP : D P ≠ 0 :=
    (mul_pos (Real.sqrt_pos.mpr (by linarith only [hPk])) (Real.log_pos hPk)).ne'
  change (D P * Δ) / (D P / D x) = D x * Δ
  rw [mul_comm (D P) Δ, mul_div_assoc, div_div_cancel₀ hDP, mul_comm Δ (D x)]

private lemma eventually_canonical_root_correction {N : ℕ → ℕ}
    (hx : Tendsto (fun k => (N k : ℝ)) atTop atTop) :
    ∀ᶠ k : ℕ in atTop,
      0 ≤ D (N k : ℝ) * (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ)) ∧
      D (N k : ℝ) * (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ)) ≤
        2 * (2 * Real.sqrt 2 + 1) := by
  have hroot : (1 : ℝ) ≤ Real.sqrt 2 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 2)
  filter_upwards [(Metric.tendsto_nhds.mp (canonical_root_correction_tendsto hx)) 1 zero_lt_one]
    with k hk
  rw [Real.dist_eq] at hk
  exact ⟨by linarith only [(abs_lt.mp hk).1, hroot],
    by linarith only [(abs_lt.mp hk).2, hroot]⟩

private lemma weight_eq_root_mul (a : ℝ) {x : ℝ} (hx : 0 < x) :
    weight a x = Real.rpow x (a - 1 / 2) * D x := by
  have he : a = (a - 1 / 2) + 1 / 2 := by ring
  calc
    weight a x = Real.rpow x ((a - 1 / 2) + 1 / 2) * Real.log x :=
      congrArg (fun b : ℝ => Real.rpow x b * Real.log x) he
    _ = Real.rpow x (a - 1 / 2) * D x := by
      rw [D, Real.sqrt_eq_rpow, Real.rpow_eq_pow, Real.rpow_add hx, mul_assoc]
      rfl

private lemma canonical_correction_tendsto {N : ℕ → ℕ}
    (hx : Tendsto (fun k => (N k : ℝ)) atTop atTop) {a : ℝ} (ha : a < 1 / 2) :
    Tendsto (fun k => weight a (N k : ℝ) *
      (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ))) atTop (𝓝 0) := by
  let C : ℝ := 2 * (2 * Real.sqrt 2 + 1)
  have hn : Tendsto (fun k => Real.rpow (N k : ℝ) (a - 1 / 2)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr ha)).comp hx
    simpa only [Function.comp_def, neg_sub, Real.rpow_eq_pow] using hh
  have hupper : Tendsto (fun k => Real.rpow (N k : ℝ) (a - 1 / 2) * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hn.mul_const C
  have hbounds : ∀ᶠ k : ℕ in atTop,
      0 ≤ weight a (N k : ℝ) * (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ)) ∧
      weight a (N k : ℝ) * (robinLogMargin (canonicalRecord (N k)) - B (N k : ℝ)) ≤
        Real.rpow (N k : ℝ) (a - 1 / 2) * C := by
    filter_upwards [eventually_canonical_root_correction hx,
      hx.eventually (eventually_gt_atTop (0 : ℝ))] with k hk hk₀
    rw [weight_eq_root_mul a hk₀, mul_assoc]
    have hpos := (Real.rpow_pos_of_pos hk₀ (a - 1 / 2)).le
    exact ⟨mul_nonneg hpos hk.1, mul_le_mul_of_nonneg_left hk.2 hpos⟩
  exact squeeze_zero' (hbounds.mono fun _ hk => hk.1) (hbounds.mono fun _ hk => hk.2) hupper

/-- On any closed upper strip with `1 / 2 ≤ Θ < 1`, the critically weighted
literal canonical Robin samples have the complete normalized zero series as
their negative oscillatory term. The endpoint has constant `2 * √2 - 2`. -/
theorem actual_canonical_samples_signed_asymptotic {Θ : ℝ}
    (hhalf : 1 / 2 ≤ Θ) (hone : Θ < 1)
    (hstrip : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ Θ)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun k =>
      ((Real.rpow (N k : ℝ) (1 - Θ) * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))) : ℝ) : ℂ) +
      (Real.exp (-Θ * Real.log (N k : ℝ)) : ℂ) * actualH (Real.log (N k : ℝ)) -
      ((if Θ = 1 / 2 then 2 * Real.sqrt 2 - 2 else 0 : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hreal : Tendsto (fun k => weight (1 - Θ) (N k : ℝ) *
      robinLogMargin (canonicalRecord (N k)) +
      Real.exp (-Θ * Real.log (N k : ℝ)) * (actualH (Real.log (N k : ℝ))).re -
      (if Θ = 1 / 2 then 2 * Real.sqrt 2 - 2 else 0)) atTop (𝓝 0) := by
    by_cases hΘ : Θ = 1 / 2
    · subst Θ
      simp only [ite_true]
      have hRH : RiemannHypothesis := by
        apply golden_right_half_strip_implies_rh
        intro ρ hzero hright hlt
        exact (not_lt_of_ge (hstrip ρ ⟨hzero, by linarith only [hright], hlt⟩)) hright
      have hB := (actual_B_rh_signed_asymptotic hRH).comp hx
      have hc := canonical_root_correction_tendsto hx
      have h := (hB.add hc).sub_const (2 * Real.sqrt 2)
      simp only [zero_add, sub_self] at h
      have hweight (x : ℝ) : weight (1 - 1 / 2) x = D x := by
        unfold weight D
        rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
      have hexp (y : ℝ) : -(1 / 2 : ℝ) * y = -y / 2 := by ring
      refine h.congr fun k => ?_
      simp only [Function.comp_def, hweight, hexp]
      ring
    · have hstrict : 1 / 2 < Θ := lt_of_le_of_ne hhalf (Ne.symm hΘ)
      have hstrip' : ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ 1 - (1 - Θ) := by
        simpa only [sub_sub_cancel] using hstrip
      have hB := actual_B_critical_strip_signed_asymptotic (1 - Θ)
        (sub_pos.mpr hone) (by linarith only [hstrict]) hstrip'
      rw [sub_sub_cancel] at hB
      have hB' : Tendsto (fun k => weight (1 - Θ) (N k : ℝ) * B (N k : ℝ) +
          Real.exp (-Θ * Real.log (N k : ℝ)) * (actualH (Real.log (N k : ℝ))).re)
          atTop (𝓝 0) := by
        apply (hB.comp (Real.tendsto_log_atTop.comp hx)).congr'
        filter_upwards [hx.eventually_gt_atTop (0 : ℝ)] with k hk
        have he : Real.exp ((1 - Θ) * Real.log (N k : ℝ)) =
            Real.rpow (N k : ℝ) (1 - Θ) := by
          rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hk, mul_comm]
        simp only [Function.comp_def, he, Real.exp_log hk, weight]
      have hc := canonical_correction_tendsto hx (a := 1 - Θ) (by linarith only [hstrict])
      have h := hB'.add hc
      rw [zero_add] at h
      refine h.congr fun k => ?_
      rw [ite_eq_right hΘ, sub_zero]
      ring
  have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
  simp only [Function.comp_def, Complex.ofReal_zero] at h
  refine h.congr fun k => ?_
  have him : (actualH (Real.log (N k : ℝ))).im = 0 :=
    (actual_complete_H_package.2.choose_spec.2.1 _).2.1
  have hre : ((actualH (Real.log (N k : ℝ))).re : ℂ) = actualH (Real.log (N k : ℝ)) := by
    apply Complex.ext <;> simp [him]
  simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, hre]

private lemma canonical_critical_approx {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hρhalf : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re)
    {N : ℕ → ℕ} (hx : Tendsto (fun k => (N k : ℝ)) atTop atTop) :
    Tendsto (fun k => weight (1 - ρ.re) (N k : ℝ) * robinLogMargin (canonicalRecord (N k)) +
      (maximalSeries actualCoeff actualZero ρ.re (Real.log (N k : ℝ))).re) atTop (𝓝 0) := by
  have hB := (actual_normalized_B_add_maximal_tendsto hρhalf hρ.2.2 hmax).comp
    (Real.tendsto_log_atTop.comp hx)
  have hB' : Tendsto (fun k => weight (1 - ρ.re) (N k : ℝ) * B (N k : ℝ) +
      (maximalSeries actualCoeff actualZero ρ.re (Real.log (N k : ℝ))).re) atTop (𝓝 0) := by
    apply hB.congr'
    filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with k hk
    have he : Real.exp ((1 - ρ.re) * Real.log (N k : ℝ)) = Real.rpow (N k : ℝ) (1 - ρ.re) := by
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hk, mul_comm]
    change Real.exp ((1 - ρ.re) * Real.log (N k : ℝ)) * Real.log (N k : ℝ) *
      B (Real.exp (Real.log (N k : ℝ))) +
      (maximalSeries actualCoeff actualZero ρ.re (Real.log (N k : ℝ))).re = _
    rw [he, Real.exp_log hk]
  have hc := canonical_correction_tendsto hx (a := 1 - ρ.re) (by linarith only [hρhalf])
  have ht := hB'.add hc
  rw [zero_add] at ht
  exact ht.congr (fun k => by ring)

/-- The critical normalization of the literal canonical records has negative
excursions bounded away from zero on every ratio-one mesh. -/
private theorem actual_canonical_samples_negative {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hρhalf : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re)
    {N : ℕ → ℕ} (hN : StrictMono N)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      Real.rpow (N k : ℝ) (1 - ρ.re) * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))) < -c := by
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  obtain ⟨hy, hgap⟩ := log_mesh_of_ratio_one hx hratio
  obtain ⟨c, hc, hpeaks⟩ := actual_maximal_series_positive_peaks hρ hρhalf hmax
  have huc : UniformContinuous (fun u => (maximalSeries actualCoeff actualZero ρ.re u).re) :=
    Complex.uniformContinuous_re.comp
      (uniformContinuous_maximalSeries actualCoeff_hasSum.summable.norm)
  exact ⟨c, hc, arbitrarily_late_negative_samples huc hy hgap
    (canonical_critical_approx hρ hρhalf hmax hx) hc hpeaks⟩

/-- Above the critical weight, canonical Robin sample values go below every
real bound at arbitrarily large sample indices. -/
theorem actual_canonical_samples_unbounded_below {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hρhalf : 1 / 2 < ρ.re) (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re)
    {N : ℕ → ℕ} (hN : StrictMono N)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1))
    {α : ℝ} (hα : 1 - ρ.re < α) :
    ∀ M : ℝ, ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧
      Real.rpow (N k : ℝ) α * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1))) < M := by
  obtain ⟨c, hc, hneg⟩ := actual_canonical_samples_negative hρ hρhalf hmax hN hratio
  have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
  let a := 1 - ρ.re
  let q := α - a
  have hq : 0 < q := sub_pos.mpr hα
  have hfactor := (tendsto_rpow_atTop hq).comp hx
  intro M K
  obtain ⟨L, hL⟩ := eventually_atTop.mp ((hfactor.eventually_gt_atTop (-M / c)).and
    (hx.eventually_gt_atTop (0 : ℝ)))
  obtain ⟨k, hk, hpeak⟩ := hneg (max K L)
  obtain ⟨hlarge, hx₀⟩ := hL k ((le_max_right K L).trans hk)
  let x : ℝ := N k
  let m := canonicalRecord (N k)
  change -M / c < Real.rpow x q at hlarge
  change 0 < x at hx₀
  change weight a x * robinLogMargin m < -c at hpeak
  have hfactorpos := Real.rpow_pos_of_pos hx₀ q
  have hbound := (div_lt_iff₀ hc).mp hlarge
  have he : α = q + a := by dsimp [q]; ring
  have hpow : Real.rpow x α = Real.rpow x q * Real.rpow x a :=
    (congrArg (Real.rpow x) he).trans (Real.rpow_add hx₀ q a)
  refine ⟨k, (le_max_left K L).trans hk, ?_⟩
  change weight α x * robinLogMargin m < M
  calc
    weight α x * robinLogMargin m = Real.rpow x q * (weight a x * robinLogMargin m) := by
      dsimp only [weight]
      rw [hpow]
      ring
    _ < Real.rpow x q * (-c) := mul_lt_mul_of_pos_left hpeak hfactorpos
    _ < M := by linarith only [hbound]

/-- An attained maximal abscissa gives the lower-bound criterion on ratio-one
meshes, including the endpoint weight `1 / 2`. -/
theorem actual_canonical_samples_lower_bound_iff {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (hmax : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ ρ.re)
    {N : ℕ → ℕ} (hN : StrictMono N)
    (hratio : Tendsto (fun k => (N (k + 1) : ℝ) / (N k : ℝ)) atTop (𝓝 1))
    {α : ℝ} (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      -C ≤ Real.rpow (N k : ℝ) α * Real.log (N k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((N k : ℝ) + 1)))) ↔
      ρ.re ≤ 1 - α := by
  constructor
  · rintro ⟨C, _, K, hbound⟩
    by_contra! hbad
    have hρhalf : 1 / 2 < ρ.re := by linarith only [hbad, hαhalf]
    have hgt : 1 - ρ.re < α := by linarith only [hbad]
    obtain ⟨k, hk, hneg⟩ :=
      actual_canonical_samples_unbounded_below hρ hρhalf hmax hN hratio hgt (-C) K
    exact (not_lt_of_ge (hbound k hk)) hneg
  · intro hgood
    obtain ⟨C, T, hC, _, hB⟩ := actual_B_critical_strip_envelope α hα hαhalf
      (fun z hz => (hmax z hz).trans hgood)
    have hx : Tendsto (fun k => (N k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop
    have hevent : ∀ᶠ k : ℕ in atTop,
        -C ≤ weight α (N k : ℝ) * robinLogMargin (canonicalRecord (N k)) := by
      filter_upwards [hx.eventually_ge_atTop T, hx.eventually_gt_atTop (1 : ℝ),
        eventually_canonical_root_correction hx] with k hk hk1 hcorr
      let x : ℝ := N k
      let m := canonicalRecord (N k)
      change T ≤ x at hk
      change 1 < x at hk1
      have hx₀ : 0 < x := by linarith only [hk1]
      have hlog := Real.log_pos hk1
      have hD : 0 < D x := mul_pos (Real.sqrt_pos.mpr hx₀) hlog
      have hW : 0 < weight α x := mul_pos (Real.rpow_pos_of_pos hx₀ _) hlog
      have hcorr₀ : 0 ≤ D x * (robinLogMargin m - B x) := hcorr.1
      have hdiff := (mul_nonneg_iff_of_pos_left hD).mp hcorr₀
      have hmargin : B x ≤ robinLogMargin m := sub_nonneg.mp hdiff
      have hBlower : -C / weight α x ≤ B x := by
        simpa only [neg_div, weight] using (abs_le.mp (hB x hk)).1
      have hscaled := (div_le_iff₀ hW).mp hBlower
      change -C ≤ weight α x * robinLogMargin m
      rw [mul_comm] at hscaled
      exact hscaled.trans (mul_le_mul_of_nonneg_left hmargin hW.le)
    obtain ⟨K, hK⟩ := eventually_atTop.mp hevent
    exact ⟨C, hC, K, hK⟩

open MeasureTheory Set
open D5.S3.Weil.Mertens

private lemma B_eq_nat_floor (x : ℝ) : B x = B (Nat.floor x : ℝ) := by
  unfold B Mertens.E₃
  rw [Nat.floor_natCast, Chebyshev.theta_eq_theta_coe_floor x]
  ring

-- On a bounded log interval only finitely many natural floor values occur.
private lemma intervalIntegrable_nat_floor_exp (g : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun v => g (Nat.floor (Real.exp v))) volume a b := by
  classical
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  let values := (Finset.range (Nat.floor (Real.exp b) + 1)).image (fun n => ‖g n‖)
  obtain ⟨M, hM⟩ := values.bddAbove
  have hg : Measurable (fun v => g (Nat.floor (Real.exp v))) :=
    (measurable_of_countable g).comp Real.continuous_exp.measurable.nat_floor
  refine Measure.integrableOn_of_bounded (μ := volume) (M := M)
    (by simp [Real.volume_Ioc]) hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := a) (b := b))]
    with v hv
  have hvb := Nat.floor_mono (Real.exp_le_exp.mpr hv.2)
  apply hM
  exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hvb), rfl⟩

private theorem eventually_canonical_log_transport :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ v : ℝ in atTop,
      v * B (Real.exp v) ≤ v * robinLogMargin (canonicalRecord (Nat.floor (Real.exp v))) ∧
      v * robinLogMargin (canonicalRecord (Nat.floor (Real.exp v))) ≤
        v * B (Real.exp v) + K * Real.exp (-v / 2) := by
  let C : ℝ := 2 * (2 * Real.sqrt 2 + 1)
  refine ⟨4 * C, by dsimp [C]; positivity, ?_⟩
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hfloor : Tendsto (fun v : ℝ => Nat.floor (Real.exp v)) atTop atTop :=
    tendsto_nat_floor_atTop.comp Real.tendsto_exp_atTop
  filter_upwards [hfloor.eventually (eventually_canonical_root_correction hN),
    eventually_ge_atTop (2 : ℝ)] with v hcorr hv
  let n := Nat.floor (Real.exp v)
  let Δ := robinLogMargin (canonicalRecord n) - B (n : ℝ)
  change 0 ≤ D (n : ℝ) * Δ ∧ D (n : ℝ) * Δ ≤ C at hcorr
  have hv₀ : 0 ≤ v := by linarith only [hv]
  have hhalf : Real.exp v / 2 ≤ (n : ℝ) := by
    have hfloor' : Real.exp v < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith only [hfloor', Real.add_one_le_exp v, hv]
  have hn : 0 < (n : ℝ) := (by positivity : 0 < Real.exp v / 2).trans_le hhalf
  have hsq : Real.exp (v / 2) ^ 2 = Real.exp v := by
    rw [pow_two, ← Real.exp_add, show v / 2 + v / 2 = v by ring]
  have hlog : v / 2 ≤ Real.log (n : ℝ) := by
    have he : 2 ≤ Real.exp (v / 2) := by
      linarith only [hv, Real.add_one_le_exp (v / 2)]
    have h := mul_le_mul_of_nonneg_right he (Real.exp_pos (v / 2)).le
    rw [← pow_two, hsq] at h
    exact (Real.le_log_iff_exp_le hn).mpr (by linarith only [h, hhalf])
  have hsqrt : Real.exp (v / 2) ≤ 2 * Real.sqrt (n : ℝ) := by
    apply (sq_le_sq₀ (Real.exp_pos _).le (by positivity)).mp
    rw [hsq, mul_pow, Real.sq_sqrt hn.le]
    linarith only [hhalf, hn]
  have hD : 0 < D (n : ℝ) :=
    mul_pos (Real.sqrt_pos.mpr hn) (by linarith only [hlog, hv])
  have hΔ : 0 ≤ Δ := (mul_nonneg_iff_of_pos_left hD).mp hcorr.1
  have hscale : Real.exp (v / 2) * v ≤ 4 * D (n : ℝ) := calc
    _ ≤ (2 * Real.sqrt (n : ℝ)) * (2 * Real.log (n : ℝ)) :=
      mul_le_mul hsqrt (by linarith only [hlog]) hv₀ (by positivity)
    _ = _ := by unfold D; ring
  have herror : v * Δ ≤ 4 * C * Real.exp (-v / 2) := by
    rw [show -v / 2 = -(v / 2) by ring, Real.exp_neg, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos (v / 2))).mpr
    calc
      _ = (Real.exp (v / 2) * v) * Δ := by ring
      _ ≤ (4 * D (n : ℝ)) * Δ := mul_le_mul_of_nonneg_right hscale hΔ
      _ = 4 * (D (n : ℝ) * Δ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcorr.2 (by norm_num)
  have hnonneg := mul_nonneg hv₀ hΔ
  dsimp only [Δ] at hnonneg herror
  rw [B_eq_nat_floor (Real.exp v)]
  change v * B (n : ℝ) ≤ v * robinLogMargin (canonicalRecord n) ∧
    v * robinLogMargin (canonicalRecord n) ≤ v * B (n : ℝ) + 4 * C * Real.exp (-v / 2)
  constructor <;> linarith only [hnonneg, herror]

/-- A fixed positive log-window of the literal canonical Robin margins has an
eventual lower bound at exponent α exactly when every actual nontrivial
zero has real part at most 1 - α. -/
theorem actual_canonical_log_window_lower_bound_iff {h α : ℝ} (hh : 0 < h)
    (hα : 0 < α) (hαhalf : α ≤ 1 / 2) :
    (∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      -C ≤ Real.exp (α * t) * (∫ u in (0 : ℝ)..h, (t + u) *
        robinLogMargin (strictInteger (firstLayerPrice ((Nat.floor (Real.exp (t + u)) : ℝ) + 1))))) ↔
      ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.re ≤ 1 - α := by
  let m (v : ℝ) := v * robinLogMargin (canonicalRecord (Nat.floor (Real.exp v)))
  change (∃ C : ℝ, 0 ≤ C ∧ ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
    -C ≤ Real.exp (α * t) * (∫ u in (0 : ℝ)..h, m (t + u))) ↔ _
  have hend (t : ℝ) : t ≤ t + h := by linarith only [hh]
  have hm (t : ℝ) : IntervalIntegrable m volume t (t + h) :=
    (intervalIntegrable_nat_floor_exp (fun n => robinLogMargin (canonicalRecord n))
      (hend t)).continuousOn_mul continuous_id.continuousOn
  have hshift (t : ℝ) : (∫ u in (0 : ℝ)..h, m (t + u)) = ∫ v in t..t + h, m v := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := h) m t
  have hcancel (t : ℝ) : Real.exp (α * t) * Real.exp (-α * t) = 1 := by
    rw [← Real.exp_add, show α * t + -α * t = 0 by ring, Real.exp_zero]
  obtain ⟨K, hK, htransport⟩ := eventually_canonical_log_transport
  constructor
  · rintro ⟨C, _, T, hbound⟩ ρ hρ
    by_contra! hbad
    let θ (v : ℝ) := v * ActualThetaTailLaplace.f v
    have hpoint : ∀ᶠ v : ℝ in atTop,
        m v ≤ -θ v + (K + 8) * Real.exp (-v / 2) := by
      filter_upwards [htransport, Real.tendsto_exp_atTop.eventually eventually_B_le_theta_tail,
        eventually_ge_atTop (0 : ℝ)] with v hv hB hv₀
      rw [← ActualThetaTailLaplace.tail_substitution v] at hB
      have hsmall : 4 * v / Real.exp v ≤ 8 * Real.exp (-v / 2) := calc
        _ ≤ (8 * Real.exp (v / 2)) / Real.exp v :=
          div_le_div_of_nonneg_right (by linarith only [Real.add_one_le_exp (v / 2)])
            (Real.exp_pos _).le
        _ = _ := by
          rw [mul_div_assoc, ← Real.exp_sub, show v / 2 - v = -v / 2 by ring]
      have hupper : v * B (Real.exp v) ≤ -θ v + 8 * Real.exp (-v / 2) := calc
        _ ≤ v * (-ActualThetaTailLaplace.f v + 4 / Real.exp v) :=
          mul_le_mul_of_nonneg_left hB hv₀
        _ = -θ v + 4 * v / Real.exp v := by dsimp [θ]; ring
        _ ≤ _ := add_le_add le_rfl hsmall
      calc
        m v ≤ v * B (Real.exp v) + K * Real.exp (-v / 2) := hv.2
        _ ≤ (-θ v + 8 * Real.exp (-v / 2)) + K * Real.exp (-v / 2) :=
          add_le_add hupper le_rfl
        _ = _ := by ring
    obtain ⟨U, hU⟩ := eventually_atTop.mp hpoint
    let L := max (max T U) (max 0 ActualThetaTailLaplace.u₀)
    let A := h * (K + 8)
    have hzero : riemannZeta ρ = 0 := by
      simpa only [D5.S3.Weil.Convention.classicalZeta] using hρ.1
    obtain ⟨t, ht, hpeak⟩ :=
      D5.S3.Weil.Mertens.CriticalThetaTailPeak.actual_theta_tail_window_peak
        (ρ := ρ) (σ := -α) (by linarith only [hbad, hαhalf]) hzero hh
        (by linarith only [hbad]) (C + A) L
    have htTU : max T U ≤ t := (le_max_left _ _).trans ht
    have htT : T ≤ t := (le_max_left T U).trans htTU
    have htU : U ≤ t := (le_max_right T U).trans htTU
    have htL : max 0 ActualThetaTailLaplace.u₀ ≤ t := (le_max_right _ _).trans ht
    have ht₀ : 0 ≤ t := (le_max_left _ _).trans htL
    have htu : ActualThetaTailLaplace.u₀ ≤ t := (le_max_right _ _).trans htL
    have hpeak' : (C + A) * Real.exp (-α * t) < ∫ v in t..t + h, θ v := by
      rw [D5.S3.Analytic.Laplace.ForwardWindowLaplace.forwardWindow_eq_intervalIntegral
        θ hh.le t, intervalIntegral.integral_comp_add_left, add_zero] at hpeak
      exact hpeak
    have hθ : IntervalIntegrable θ volume t (t + h) := by
      have hf : IntervalIntegrable ActualThetaTailLaplace.f volume t (t + h) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hend t)]
        exact (ActualThetaTailLaplace.actual_theta_tail_laplace_ode.2.2.2.2.1).mono_set
          (fun _ hv => htu.trans_lt hv.1)
      exact hf.continuousOn_mul continuous_id.continuousOn
    let E := (K + 8) * Real.exp (-α * t)
    have hE : IntervalIntegrable (fun _ : ℝ => E) volume t (t + h) := intervalIntegrable_const
    have hi := intervalIntegral.integral_mono_on (hend t) (hm t) (hθ.neg.add hE)
      (fun v hv => (hU v (htU.trans hv.1)).trans (by
        have he : Real.exp (-v / 2) ≤ Real.exp (-α * t) := by
          apply Real.exp_le_exp.mpr
          linarith only [hv.1, mul_le_mul_of_nonneg_right hαhalf ht₀]
        change -θ v + (K + 8) * Real.exp (-v / 2) ≤ -θ v + E
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left he (by linarith only [hK]))))
    rw [intervalIntegral.integral_add hθ.neg hE] at hi
    change (∫ v in t..t + h, m v) ≤
      (∫ v in t..t + h, -θ v) + (∫ _ in t..t + h, E) at hi
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const, smul_eq_mul,
      add_sub_cancel_left] at hi
    have hscaled := mul_le_mul_of_nonneg_left hi (Real.exp_pos (α * t)).le
    have herror : Real.exp (α * t) * (h * E) = A := calc
      _ = A * (Real.exp (α * t) * Real.exp (-α * t)) := by dsimp [A, E]; ring
      _ = _ := by rw [hcancel, mul_one]
    rw [mul_add, mul_neg, herror] at hscaled
    have hp := mul_lt_mul_of_pos_left hpeak' (Real.exp_pos (α * t))
    rw [mul_left_comm (Real.exp (α * t)), hcancel, mul_one] at hp
    have hlower := hbound t htT
    rw [hshift] at hlower
    linarith only [hlower, hscaled, hp]
  · intro hstrip
    obtain ⟨C, X, hC, _, hB⟩ := actual_B_critical_strip_envelope α hα hαhalf hstrip
    have hpoint : ∀ᶠ v : ℝ in atTop, -C * Real.exp (-α * v) ≤ m v := by
      filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop X,
        eventually_gt_atTop (0 : ℝ), htransport] with v hv hv₀ hc
      have hraw := (abs_le.mp (hB (Real.exp v) hv)).1
      rw [← neg_div, Real.rpow_eq_pow, ← Real.exp_mul, mul_comm v α, Real.log_exp] at hraw
      have hw : 0 < Real.exp (α * v) * v := mul_pos (Real.exp_pos _) hv₀
      have hscaled := (div_le_iff₀ hw).mp hraw
      have hBlower : -C * Real.exp (-α * v) ≤ v * B (Real.exp v) := by
        apply (mul_le_mul_iff_of_pos_left (Real.exp_pos (α * v))).mp
        rw [mul_left_comm (Real.exp (α * v)), hcancel, mul_one]
        calc
          _ ≤ B (Real.exp v) * (Real.exp (α * v) * v) := hscaled
          _ = _ := by ring
      exact hBlower.trans hc.1
    obtain ⟨T, hT⟩ := eventually_atTop.mp hpoint
    refine ⟨h * C, mul_nonneg hh.le hC, T, fun t ht => ?_⟩
    have hconst : IntervalIntegrable (fun _ : ℝ => -C * Real.exp (-α * t))
        volume t (t + h) := intervalIntegrable_const
    have hi := intervalIntegral.integral_mono_on (hend t) hconst (hm t) (fun v hv => by
      have he : Real.exp (-α * v) ≤ Real.exp (-α * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hv.1 (neg_nonpos.mpr hα.le))
      exact (mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hC)).trans (hT v (ht.trans hv.1)))
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at hi
    have hscaled := mul_le_mul_of_nonneg_left hi (Real.exp_pos (α * t)).le
    have hnormalize : Real.exp (α * t) * (h * (-C * Real.exp (-α * t))) = -(h * C) := calc
      _ = -(h * C) * (Real.exp (α * t) * Real.exp (-α * t)) := by ring
      _ = _ := by rw [hcancel, mul_one]
    rw [hnormalize] at hscaled
    rw [hshift]
    exact hscaled

open CanonicalThresholdWindowTransfer (tailScale)
open D5.S3.Weil.Mertens.ActualThetaTailLaplace (F)
open D5.S3.Arith.Robin.Analytic.ThetaReparametrizedSandwich
  (actual_theta_reparametrized_sandwich actual_theta_tail_local_modulus)
open ActualRecordAllLogBudgetRemainder (exists_actual_theta_crossing_sampler)

private abbrev canonicalMargin (n : ℕ) := robinLogMargin (canonicalRecord n)

private lemma eventually_canonical_correction :
    ∀ᶠ n : ℕ in atTop, 0 ≤ D (n : ℝ) * (canonicalMargin n - B (n : ℝ)) ∧
      D (n : ℝ) * (canonicalMargin n - B (n : ℝ)) ≤ 2 * (2 * Real.sqrt 2 + 1) := by
  exact eventually_canonical_root_correction
    (N := id) (tendsto_natCast_atTop_atTop (R := ℝ))

private lemma eventually_D_le_id : ∀ᶠ x : ℝ in atTop, D x ≤ x := by
  have h := (_root_.isLittleO_log_rpow_atTop one_half_pos).tendsto_div_nhds_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  change Real.log x / x ^ (1 / 2 : ℝ) < 1 at hx
  rw [← Real.sqrt_eq_rpow] at hx
  have hs := Real.sqrt_pos.mpr hx0
  have hl := (div_lt_iff₀ hs).mp hx
  rw [one_mul] at hl
  calc
    D x ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_left hl.le hs.le
    _ = x := Real.mul_self_sqrt hx0.le

private lemma root_error_eventually_le_tail {b c L : ℝ} (hb : 1 / 2 < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, L / D x ≤ (c / 2) * tailScale b x := by
  have he : Tendsto (fun x : ℝ => L * x ^ (1 / 2 - b : ℝ)) atTop (𝓝 0) := by
    simpa only [neg_sub, mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hb)).const_mul L
  filter_upwards [he.eventually_lt_const (half_pos hc), eventually_gt_atTop (1 : ℝ)]
    with x hx hx1
  have hx0 : 0 < x := by linarith
  have hfactor : L / D x = (L * x ^ (1 / 2 - b : ℝ)) * tailScale b x := by
    rw [D, tailScale, Real.sqrt_eq_rpow, ← mul_div_assoc, mul_assoc, ← Real.rpow_add hx0]
    rw [show 1 / 2 - b + (b - 1) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx0.le]
    ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right hx.le
    (div_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_pos hx1).le)

private lemma eventually_tailScale_sample_le {n : ℝ → ℕ} {b : ℝ}
    (hratio : Tendsto (fun x : ℝ => (n x : ℝ) / x) atTop (𝓝 1))
    (hshift : Tendsto (fun x : ℝ => Real.log (n x : ℝ) - Real.log x) atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop, tailScale b (n x : ℝ) ≤ 2 * tailScale b x := by
  have h := (CanonicalThresholdWindowTransfer.tendsto_tailScale_ratio b hratio hshift).eventually
    (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hpos : 0 < tailScale b x := by
    unfold tailScale
    exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hx1)
  exact ((div_lt_iff₀ hpos).mp hx).le

private theorem eventually_positive_canonical_sample {n : ℝ → ℕ}
    (hsample : ∀ᶠ x : ℝ in atTop,
      2 ≤ n x ∧ Chebyshev.theta ((n x - 1 : ℕ) : ℝ) ≤ x ∧
      x < Chebyshev.theta (n x : ℝ) ∧
      Chebyshev.theta (n x : ℝ) - x ≤ Real.log (n x : ℝ) ∧
      ∀ m : ℕ, x < Chebyshev.theta (m : ℝ) → n x ≤ m)
    (hratio : Tendsto (fun x : ℝ => (n x : ℝ) / x) atTop (𝓝 1))
    (hshift : Tendsto (fun x : ℝ => Real.log (n x : ℝ) - Real.log x) atTop (𝓝 0)) :
    ∀ᶠ x : ℝ in atTop, -F x - 12 / D x ≤ canonicalMargin (n x) := by
  have hratioHalf := hratio.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hcastTop : Tendsto (fun x : ℝ => (n x : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [hratioHalf, eventually_gt_atTop (max 1 (2 * a))] with x hr hx
    have hx0 := zero_lt_one.trans_le ((le_max_left _ _).trans hx.le)
    have hlow := (lt_div_iff₀ hx0).mp (Set.mem_Ioi.mp hr)
    linarith only [hlow, (le_max_right _ _).trans hx.le]
  have hnTop : Tendsto n atTop atTop := tendsto_natCast_atTop_iff.mp hcastTop
  filter_upwards [hsample, hratioHalf, hshift.eventually_lt_const zero_lt_one,
    hnTop.eventually eventually_canonical_correction, actual_theta_tail_local_modulus,
    eventually_D_le_id, eventually_gt_atTop (max 4 (Real.exp 1))] with x hs hr hshiftx
      hcorr hmod hDx hx
  let N := n x
  have hx4 : 4 < x := (le_max_left _ _).trans_lt hx
  have hx0 : 0 < x := by linarith
  have hxlog : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hx.le)
  have hNlow : x / 2 < (N : ℝ) := by
    have h := (lt_div_iff₀ hx0).mp (Set.mem_Ioi.mp hr)
    linarith only [h]
  have hN2 : 2 < (N : ℝ) := by linarith only [hx4, hNlow]
  have hθ : 2 < Chebyshev.theta (N : ℝ) := (by linarith : 2 < x).trans hs.2.2.1
  have hlogx : 0 < Real.log x := by linarith only [hxlog]
  have hDxPos : 0 < D x := mul_pos (Real.sqrt_pos.mpr hx0) hlogx
  have hD : 0 < D (N : ℝ) :=
    mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos (by linarith))
  have hG : B (N : ℝ) ≤ canonicalMargin N :=
    sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hD).mp hcorr.1)
  have hB := (actual_theta_reparametrized_sandwich hN2 hθ).1
  have hE := (abs_le.mp (finite_cancellation hN2.le)).1
  have hF := hmod (Chebyshev.theta (N : ℝ)) hs.2.2.1.le
  have hLog : Real.log (N : ℝ) ≤ 2 * Real.log x := by linarith only [hshiftx, hxlog]
  have hmove : F (Chebyshev.theta (N : ℝ)) - F x ≤ 4 / x := by
    refine (le_abs_self _).trans (hF.trans ?_)
    apply (div_le_iff₀ (mul_pos hx0 (by linarith))).2
    rw [show (4 / x) * (x * Real.log x) = 4 * Real.log x by field_simp]
    linarith only [hs.2.2.2.1, hLog]
  have hcost : 4 / (N : ℝ) ≤ 8 / x := by
    calc
      _ ≤ 4 / (x / 2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hNlow.le
      _ = _ := by ring
  have hroot : 12 / x ≤ 12 / D x :=
    div_le_div_of_nonneg_left (by norm_num) hDxPos hDx
  have hsum : 4 / x + 8 / x = 12 / x := by ring
  linarith only [hG, hB, hE, hmove, hcost, hroot, hsum]

private theorem eventually_negative_canonical_sample :
    ∀ᶠ x : ℝ in atTop, canonicalMargin ⌈x⌉₊ ≤
      -F x + (6 + 2 * (2 * Real.sqrt 2 + 1)) / D x := by
  have hθ := D5.S3.Arith.Robin.EulerLayerRootCorrection.prime_number_limits.2
  have hθTop : Tendsto Chebyshev.theta atTop atTop := by
    apply (hθ.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) tendsto_id).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_mul_cancel₀ _ hx.ne'
  filter_upwards [eventually_gt_atTop (max 2 (Real.exp 1)), hθTop.eventually_gt_atTop 2,
    tendsto_nat_ceil_atTop.eventually eventually_canonical_correction,
    actual_theta_tail_local_modulus,
    eventually_D_le_id] with x hx hθx hcorr hmod hDx
  let N : ℕ := ⌈x⌉₊
  have hx2 : 2 < x := (le_max_left _ _).trans_lt hx
  have hx0 : 0 < x := by linarith
  have hN := Nat.le_ceil x
  have hN2 : 2 < (N : ℝ) := hx2.trans_le hN
  have hNclose : (N : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hD : 0 < D x := mul_pos (Real.sqrt_pos.mpr hx0) hlogx
  have hD_N : D x ≤ D (N : ℝ) := by
    unfold D
    exact mul_le_mul (Real.sqrt_le_sqrt hN) (Real.log_le_log hx0 hN)
      (Real.log_pos (by linarith)).le (Real.sqrt_nonneg _)
  have hDpos := hD.trans_le hD_N
  let L : ℝ := 2 * (2 * Real.sqrt 2 + 1)
  have hG : canonicalMargin N - B (N : ℝ) ≤ L / D x := by
    have h : canonicalMargin N - B (N : ℝ) ≤ L / D (N : ℝ) := by
      apply (le_div_iff₀ hDpos).2
      rw [mul_comm]
      exact hcorr.2
    exact h.trans (div_le_div_of_nonneg_left (by unfold L; positivity) hD hD_N)
  have hB := (actual_theta_reparametrized_sandwich hN2
    (hθx.trans_le (Chebyshev.theta_mono hN))).2
  have hE := (abs_le.mp (finite_cancellation hN2.le)).2
  have hcost : 4 / (N : ℝ) ≤ 4 / D x :=
    div_le_div_of_nonneg_left (by norm_num) hD (hDx.trans hN)
  have hmove : F x - F (N : ℝ) ≤ 2 / D x := by
    have hLocal := (neg_le_abs _).trans (hmod (N : ℝ) hN)
    rw [neg_sub] at hLocal
    have hden : D x ≤ x * Real.log x := by
      unfold D
      have hs : Real.sqrt x ≤ x := by
        simpa only [Real.sqrt_sq (by linarith : 0 ≤ x)] using
          Real.sqrt_le_sqrt (show x ≤ x ^ 2 by nlinarith)
      exact mul_le_mul_of_nonneg_right hs (Real.log_pos (by linarith)).le
    calc
      _ ≤ 2 * ((N : ℝ) - x) / (x * Real.log x) := hLocal
      _ ≤ 2 / (x * Real.log x) :=
        div_le_div_of_nonneg_right (by linarith) (mul_nonneg hx0.le hlogx.le)
      _ ≤ 2 / D x := div_le_div_of_nonneg_left (by norm_num) hD hden
  have hsum : 2 / D x + 4 / D x + L / D x = (6 + L) / D x := by ring
  change canonicalMargin N ≤ -F x + (6 + L) / D x
  linarith only [hG, hB, hE, hcost, hmove, hsum]

open D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open D5.S3.Arith.Robin.Analytic.ActualUnattainedThetaWindows
open CanonicalThresholdWindowTransfer (normalizedMargin)

private theorem theta_windows_at_prescribed_scale {b h : ℝ}
    (hb : 1 / 2 < b) (hbΘ : b < zeroAbscissa) (hh : 0 < h)
    (hun : ∀ z : ℂ, IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      (∃ t ∈ Icc T (T + h), c * tailScale b (Real.exp t) ≤ -F (Real.exp t)) ∧
      (∃ t ∈ Icc T (T + h), c * tailScale b (Real.exp t) ≤ F (Real.exp t)) := by
  obtain ⟨β, hβb, hβ₁, c, hc, hwindow⟩ :=
    eventually_actual_weighted_theta_tail_two_signs hb hbΘ hh hun
  refine ⟨c, hc, ?_⟩
  filter_upwards [hwindow, eventually_gt_atTop (0 : ℝ)] with T hwin hT
  have hscale (t : ℝ) (ht : T ≤ t) :
      c * tailScale b (Real.exp t) ≤ c * Real.exp ((β - 1) * T) / T := by
    have hExp : Real.exp ((b - 1) * t) ≤ Real.exp ((β - 1) * T) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonpos_left ht (sub_nonpos.mpr (hβb.trans hβ₁).le)).trans
        (mul_le_mul_of_nonneg_right (sub_le_sub_right hβb.le 1) hT.le)
    rw [tailScale, Real.log_exp, ← Real.exp_mul, mul_comm t, ← mul_div_assoc]
    exact (div_le_div_of_nonneg_left (by positivity) hT ht).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hExp hc.le) hT.le)
  obtain ⟨⟨p, hp, hpF⟩, ⟨m, hm, hmF⟩⟩ := hwin
  exact ⟨⟨p, hp, (hscale p hp.1).trans hpF.le⟩,
    ⟨m, hm, (hscale m hm.1).trans (by linarith only [hmF])⟩⟩

private theorem eventually_sample_transfer {n : ℝ → ℕ} {L b : ℝ}
    (G : ℕ → ℝ) (K : ℝ → ℝ) (hb : 1 / 2 < b)
    (hbound : ∀ᶠ x : ℝ in atTop, K x - L / D x ≤ G (n x))
    (hratio : Tendsto (fun x : ℝ => (n x : ℝ) / x) atTop (𝓝 1))
    (hshift : Tendsto (fun x : ℝ => Real.log (n x : ℝ) - Real.log x) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, c * tailScale b x ≤ K x →
      (c / 4) * tailScale b (n x : ℝ) ≤ G (n x) := by
  filter_upwards [hbound, root_error_eventually_le_tail (L := L) hb hc,
    eventually_tailScale_sample_le (b := b) hratio hshift] with x hx he hs hw
  have hscale := mul_le_mul_of_nonneg_left hs (show 0 ≤ c / 4 by positivity)
  have hdouble : c / 4 * (2 * tailScale b x) = c / 2 * tailScale b x := by ring
  have hmargin : c * tailScale b x = 2 * ((c / 2) * tailScale b x) := by ring
  rw [hdouble] at hscale
  rw [hmargin] at hw
  linarith only [hx, he, hscale, hw]

/-- Under unattainment, actual canonical Robin records admit two strictly increasing
integer meshes with adjacent ratios tending to one. For any exponent `α` between
`1 - zeroAbscissa` and `1/2`, the literal normalized margins tend to opposite infinities. -/
theorem actual_canonical_two_signed_ratio_one_meshes {α : ℝ}
    (hα : 1 - zeroAbscissa < α) (hαhalf : α < 1 / 2)
    (hun : ∀ z : ℂ, IsNontrivialZero z → z.re < zeroAbscissa) :
    ∃ Npos Nneg : ℕ → ℕ, StrictMono Npos ∧ StrictMono Nneg ∧
      Tendsto (fun k => (Npos (k + 1) : ℝ) / (Npos k : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun k => (Nneg (k + 1) : ℝ) / (Nneg k : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun k => weight α (Npos k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((Npos k : ℝ) + 1)))) atTop atTop ∧
      Tendsto (fun k => weight α (Nneg k : ℝ) *
        robinLogMargin (strictInteger (firstLayerPrice ((Nneg k : ℝ) + 1)))) atTop atBot := by
  obtain ⟨b, hb, hbΘ⟩ := exists_between (by linarith only [hα] : 1 - α < zeroAbscissa)
  have hbHalf : 1 / 2 < b := by linarith only [hb, hαhalf]
  have hexponent : 0 < α + b - 1 := by linarith only [hb]
  let δ := (α + b - 1) / 2
  obtain ⟨n, hn, hratio, hlog⟩ := exists_actual_theta_crossing_sampler
  let m : ℝ → ℕ := Nat.ceil
  have hmRatio : Tendsto (fun x : ℝ => (m x : ℝ) / x) atTop (𝓝 1) :=
    tendsto_nat_ceil_div_atTop
  have hmLog : Tendsto (fun x : ℝ => Real.log (m x : ℝ) - Real.log x) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).tendsto.comp hmRatio
    rw [Real.log_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx₀ : 0 < x := by linarith
    exact Real.log_div (hx₀.trans_le (Nat.le_ceil x)).ne' hx₀.ne'
  have hpos := eventually_sample_transfer canonicalMargin (fun x => -F x) hbHalf
    (eventually_positive_canonical_sample hn hratio hlog) hratio hlog
  have hnegBound : ∀ᶠ x : ℝ in atTop,
      F x - (6 + 2 * (2 * Real.sqrt 2 + 1)) / D x ≤ -canonicalMargin (m x) := by
    filter_upwards [eventually_negative_canonical_sample] with x hx
    change canonicalMargin (m x) ≤ -F x + (6 + 2 * (2 * Real.sqrt 2 + 1)) / D x at hx
    linarith only [hx]
  have hneg := eventually_sample_transfer (fun n => -canonicalMargin n) F hbHalf
    hnegBound hmRatio hmLog
  have hwindow : ∀ h : ℝ, 0 < h → ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      (∃ t ∈ Icc T (T + h), c * tailScale b (Real.exp t) ≤ -F (Real.exp t)) ∧
      (∃ t ∈ Icc T (T + h), c * tailScale b (Real.exp t) ≤ -(-F (Real.exp t))) := by
    intro h hh
    simpa only [neg_neg] using theta_windows_at_prescribed_scale hbHalf hbΘ hh hun
  obtain ⟨_, _, np, nm, hnp, hnm, _, _, hrp, hrm, hlimp, hlimm⟩ :=
    CanonicalThresholdWindowTransfer.threshold_grids_of_two_signed_samplings
      (δ := δ) (half_pos hexponent) (half_lt_self hexponent)
      (fun x => -F x) canonicalMargin n m hwindow hratio hmRatio hlog hmLog hpos
      (by simpa only [neg_neg] using hneg)
  exact ⟨np, nm, hnp, hnm, hrp, hrm, hlimp, hlimm⟩

end D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap
