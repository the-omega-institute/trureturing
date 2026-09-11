/- GID: D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/CanonicalLiGrowthZeroFree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Growth of the actual derivative-defined Li coefficients gives a global xi differential equation, right-half-plane zero-freeness and Mathlib RiemannHypothesis. -/

import D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
import D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
import D5.S3.Zeros.ActualZeroGeometry

/-!
The canonical coefficients and their local expansion are imported from the
merged loning-bot PR #6172, not supplied as an oracle or defined a second time.
The disk function is the actual xiReading composed with (1-z)^(-1).

The global growth premise is NOT proved here. The implication is the analytic
consumer of the preceding probability lane's all-index quadratic bound once
that lane's L is instantiated by canonicalLiCoefficient. No assumption named
liCriterion, global logarithmic expansion, no-zero condition or RH is used.
The final zero transfer and reflection/trivial-zero treatment reuse existing
actual Riemann-zeta bridge theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree

open Filter Set
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
open D5.S3.Zeros.ActualZeroGeometry
open D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
open scoped Topology BigOperators NNReal

/-- The sum of the existing canonical coefficients, with no change of indexing. -/
def canonicalLiSeries (z : ℂ) : ℂ :=
  ∑' n : ℕ, (canonicalLiCoefficient (n + 1) : ℂ) * z ^ n

/-- The actual entire xiReading under the standard disk-to-half-plane map. -/
def canonicalXiDisk (z : ℂ) : ℂ := xiReading ((1 - z)⁻¹)

private theorem disk_ne_one {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) : z ≠ 1 := by
  intro h
  subst z
  norm_num [Metric.mem_ball] at hz

/-- The transformed actual xi function is analytic on the whole unit disk,
without any zero-location hypothesis. -/
theorem canonical_xi_disk_analytic :
    AnalyticOnNhd ℂ canonicalXiDisk (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have inverseAnalytic : AnalyticAt ℂ (fun w : ℂ => (1 - w)⁻¹) z :=
    (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr (disk_ne_one hz).symm)
  exact (xi_reading_differentiable.analyticAt ((1 - z)⁻¹)).comp
    (f := fun w : ℂ => (1 - w)⁻¹) inverseAnalytic

private theorem canonical_xi_disk_derivative (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    deriv canonicalXiDisk z = (1 - z)⁻¹ ^ 2 * deriv xiReading ((1 - z)⁻¹) := by
  have innerDerivative : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
    simpa [inv_pow] using
      (((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).fun_inv
        (sub_ne_zero.mpr (disk_ne_one hz).symm))
  have chain := (xi_reading_differentiable ((1 - z)⁻¹)).hasDerivAt.comp z innerDerivative
  change HasDerivAt canonicalXiDisk
    (deriv xiReading ((1 - z)⁻¹) * (1 - z)⁻¹ ^ 2) z at chain
  exact chain.deriv.trans (mul_comm _ _)

/-- The merged canonical local series gives the actual local differential
identity. Nonvanishing is used only near the already known value xi(1)=1/2. -/
theorem canonical_xi_disk_local_equation :
    deriv canonicalXiDisk =ᶠ[𝓝 (0 : ℂ)]
      (fun z => canonicalLiSeries z * canonicalXiDisk z) := by
  have origin : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have initial : canonicalXiDisk 0 ≠ 0 := by
    norm_num [canonicalXiDisk, xi_reading_endpoint_values.2]
  have nearNonzero := (canonical_xi_disk_analytic 0 origin).continuousAt.eventually_ne initial
  filter_upwards [canonical_li_local_expansion, nearNonzero,
    Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z series nonzero hz
  have sum_eq : canonicalLiSeries z =
      (1 - z) ^ (-2 : ℤ) * logDeriv xiReading (1 / (1 - z)) := series.tsum_eq
  rw [canonical_xi_disk_derivative z hz, sum_eq]
  change xiReading ((1 - z)⁻¹) ≠ 0 at nonzero
  simp only [canonicalXiDisk, zpow_neg, zpow_ofNat, inv_pow, one_div, logDeriv_apply]
  rw [mul_assoc, div_mul_cancel₀ _ nonzero]

/-- Full absolute convergence of the ORIGINAL canonical series produces its
actual global differential identity and excludes all disk zeros. -/
theorem canonical_li_summable_disk_zero_free
    (summable : ∀ r : ℝ≥0, r < 1 →
      Summable (fun n : ℕ => |canonicalLiCoefficient (n + 1)| * (r : ℝ) ^ n)) :
    AnalyticOnNhd ℂ canonicalLiSeries (Metric.ball (0 : ℂ) 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      deriv canonicalXiDisk z = canonicalLiSeries z * canonicalXiDisk z) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, canonicalXiDisk z ≠ 0) := by
  have seriesAnalytic : AnalyticOnNhd ℂ canonicalLiSeries (Metric.ball (0 : ℂ) 1) := by
    apply scalar_series_analytic_unit_disk (fun n => (canonicalLiCoefficient (n + 1) : ℂ))
    intro r hr
    simpa only [Complex.norm_real, Real.norm_eq_abs] using summable r hr
  have origin : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have initial : canonicalXiDisk 0 ≠ 0 := by
    norm_num [canonicalXiDisk, xi_reading_endpoint_values.2]
  exact ⟨seriesAnalytic, local_logarithmic_equation_zero_free
    Metric.isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    canonical_xi_disk_analytic seriesAnalytic origin initial canonical_xi_disk_local_equation⟩

/-- Bare actual disk nonvanishing implies whole-half-plane nonvanishing. -/
theorem xi_disk_zero_free_right_half_plane
    (diskFree : ∀ z ∈ Metric.ball (0 : ℂ) 1, canonicalXiDisk z ≠ 0) :
    ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0 := by
  intro s hs
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have smaller : Complex.normSq (s - 1) < Complex.normSq s := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero]
    nlinarith
  have normSmaller : ‖s - 1‖ < ‖s‖ := by
    simp only [Complex.normSq_eq_norm_sq] at smaller
    nlinarith [norm_nonneg (s - 1), norm_nonneg s]
  let z : ℂ := 1 - s⁻¹
  have quotient : z = (s - 1) / s := by dsimp [z]; field_simp [hs0]
  have inDisk : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, quotient, norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hs0)).mpr normSmaller
  have inverse : (1 - z)⁻¹ = s := by
    dsimp [z]
    rw [show (1 : ℂ) - (1 - s⁻¹) = s⁻¹ by ring, inv_inv]
  have nonzero := diskFree z inDisk
  simpa only [canonicalXiDisk, inverse] using nonzero

/-- The bare converse contains no Li coefficient or summability hypothesis. -/
theorem xi_disk_zero_free_implies_rh
    (diskFree : ∀ z ∈ Metric.ball (0 : ℂ) 1, canonicalXiDisk z ≠ 0) :
    RiemannHypothesis :=
  rh_iff_xi_right_half_plane.mpr (xi_disk_zero_free_right_half_plane diskFree)

/-- Summability supplies disk nonvanishing, then the bare geometric bridge. -/
theorem canonical_li_summable_right_half_plane
    (summable : ∀ r : ℝ≥0, r < 1 →
      Summable (fun n : ℕ => |canonicalLiCoefficient (n + 1)| * (r : ℝ) ^ n)) :
    ∀ s : ℂ, (1 : ℝ) / 2 < s.re → xiReading s ≠ 0 :=
  xi_disk_zero_free_right_half_plane (canonical_li_summable_disk_zero_free summable).2.2

/-- The actual canonical series condition implies Mathlib's RiemannHypothesis.
The existing xi/nontrivial-zero bridge and right-half-strip reflection result
handle the arithmetic endpoints; no abstract Li-criterion premise is present. -/
theorem canonical_li_disk_summability_implies_rh
    (summable : ∀ r : ℝ≥0, r < 1 →
      Summable (fun n : ℕ => |canonicalLiCoefficient (n + 1)| * (r : ℝ) ^ n)) :
    RiemannHypothesis :=
  xi_disk_zero_free_implies_rh (canonical_li_summable_disk_zero_free summable).2.2

/-- The all-index quadratic bound supplied by the probability route suffices
for the ACTUAL derivative-defined coefficients. The bound is still a premise. -/
theorem canonical_li_quadratic_growth_implies_rh (C : ℝ)
    (bound : ∀ n : ℕ, |canonicalLiCoefficient n| ≤ C * (n : ℝ) ^ 2) :
    RiemannHypothesis := by
  apply canonical_li_disk_summability_implies_rh
  intro r hr
  have h := quadratic_coefficients_summable
    (fun n => (canonicalLiCoefficient (n + 1) : ℂ)) C
    (fun n => by simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_add,
      Nat.cast_one] using bound (n + 1)) r hr
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

/-- Direct consumer for the preceding probability lane's normalized quadratic
envelope, after using exactly canonicalLiCoefficient as its sequence. -/
theorem canonical_li_probability_envelope_implies_rh
    (envelope : ∀ n : ℕ, 0 ≤ canonicalLiCoefficient n ∧
      canonicalLiCoefficient n ≤ canonicalLiCoefficient 1 * (n : ℝ) ^ 2) :
    RiemannHypothesis := by
  apply canonical_li_quadratic_growth_implies_rh (canonicalLiCoefficient 1)
  intro n
  simpa only [abs_of_nonneg (envelope n).1] using (envelope n).2

/-- A failed RH cannot coexist with any all-index absolute quadratic bound.
This is a contrapositive certificate, not a finite check of the growth premise. -/
theorem not_rh_forces_quadratic_escape (failure : ¬ RiemannHypothesis) (C : ℝ) :
    ∃ n : ℕ, C * (n : ℝ) ^ 2 < |canonicalLiCoefficient n| := by
  by_contra! bounded
  exact failure (canonical_li_quadratic_growth_implies_rh C bounded)

#print axioms canonical_xi_disk_local_equation
#print axioms canonical_li_summable_right_half_plane
#print axioms canonical_li_quadratic_growth_implies_rh
#print axioms canonical_li_probability_envelope_implies_rh

end D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree
