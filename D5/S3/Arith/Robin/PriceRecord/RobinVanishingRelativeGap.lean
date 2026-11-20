/- GID: D5/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RobinVanishingRelativeGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An attained maximal zeta zero gives the Robin lower-bound criterion on ratio-one meshes. -/

import D5.S3.Analytic.Asymptotics.VanishingGapSignTransfer
import D5.S3.Analytic.Laplace.MaximalRealPartProjection
import D5.S3.Arith.Robin.ActualTwoPriceDefect
import D5.S3.Arith.Robin.Analytic.LogLogGlobalCurvature
import D5.S3.Arith.Robin.Analytic.ZeroFreeStripMertensEnvelope
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

end D5.S3.Arith.Robin.PriceRecord.RobinVanishingRelativeGap
