/- GID: D5/S3/Weil/Probability/CanonicalLiRadiusObstruction
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/CanonicalLiRadiusObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An actual xi disk zero forces canonical Li coefficients to escape every exponential envelope beyond that zero's radius, in every tail. -/

import D5.S3.Weil.Probability.CanonicalLiDiskEquivalence

/-!
All coefficient readouts use the existing canonicalLiCoefficient. The local
cross-multiplied equation is reused. An eventual coefficient envelope supplies
an analytic disk by the pinned formal-series radius theorem, so a putative
zero within that disk is excluded by the existing analytic-order argument.
Contraposition yields explicit radius-dependent growth, with no claimed index
cutoff and without supposing the existence of an off-critical zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.CanonicalLiRadiusObstruction

open Filter Set
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues
open D5.S3.Zeros.Endpoints.CanonicalLiLocalExpansion
open D5.S3.Weil.Probability.AnalyticLogarithmicContinuation
open D5.S3.Weil.Probability.CanonicalLiGrowthZeroFree
open D5.S3.Weil.Probability.CanonicalLiDiskEquivalence
open scoped Topology BigOperators NNReal ENNReal

/-- An eventual weighted coefficient bound gives analyticity on the original
radius disk. A finite initial segment is irrelevant to this radius statement. -/
theorem scalar_series_analytic_of_eventual_bound (a : ℕ → ℂ) (R : ℝ≥0) (C : ℝ)
    (bound : ∀ᶠ n : ℕ in atTop, ‖a n‖ * (R : ℝ) ^ n ≤ C) :
    AnalyticOnNhd ℂ (fun z : ℂ => ∑' n, a n * z ^ n) (Metric.ball 0 (R : ℝ)) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a
  have radius : (R : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_eventually_le C
    simpa only [p, FormalMultilinearSeries.ofScalars_norm] using bound
  have sum_eq : p.sum = (fun z : ℂ => ∑' n, a n * z ^ n) := by
    funext z
    simp only [p, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [← sum_eq]
  intro z hz
  apply (FormalMultilinearSeries.analyticOnNhd (p := p))
  have hn : ‖z‖₊ < R := by
    exact_mod_cast (show ‖z‖ < (R : ℝ) from by
      simpa only [Metric.mem_ball, dist_zero_right] using hz)
  have he : edist z 0 < (R : ℝ≥0∞) := by
    rw [edist_nndist, nndist_zero_right]
    exact_mod_cast hn
  exact he.trans_le radius

/-- At any radius at most one, an eventual bound on the ACTUAL canonical
coefficients excludes all actual xi disk zeros strictly within that radius. -/
theorem canonical_weighted_tail_bound_zero_free (R : ℝ≥0)
    (positiveR : 0 < R) (withinDisk : R ≤ 1) (C : ℝ)
    (bound : ∀ᶠ n : ℕ in atTop,
      |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n ≤ C) :
    ∀ z ∈ Metric.ball (0 : ℂ) (R : ℝ), canonicalXiDisk z ≠ 0 := by
  have analyticG : AnalyticOnNhd ℂ canonicalLiSeries (Metric.ball (0 : ℂ) (R : ℝ)) := by
    apply scalar_series_analytic_of_eventual_bound
      (fun n => (canonicalLiCoefficient (n + 1) : ℂ)) R C
    simpa only [Complex.norm_real, Real.norm_eq_abs] using bound
  have subset : Metric.ball (0 : ℂ) (R : ℝ) ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (show (R : ℝ) ≤ 1 from withinDisk)
  have origin : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (R : ℝ) := by
    simpa using (show (0 : ℝ) < R from positiveR)
  have initial : canonicalXiDisk 0 ≠ 0 := by
    norm_num [canonicalXiDisk, xi_reading_endpoint_values.2]
  exact (local_logarithmic_equation_zero_free Metric.isOpen_ball
    (convex_ball (0 : ℂ) (R : ℝ)).isPreconnected
    (canonical_xi_disk_analytic.mono subset) analyticG origin initial
    canonical_xi_disk_local_equation).2

/-- A specified actual disk zero forces arbitrarily large weighted canonical
coefficients in EVERY tail, at each larger radius no greater than one. -/
theorem disk_zero_forces_weighted_tail_escape (z : ℂ) (zero : canonicalXiDisk z = 0)
    (R : ℝ≥0) (inside : ‖z‖ < (R : ℝ)) (withinDisk : R ≤ 1)
    (N : ℕ) (C : ℝ) :
    ∃ n : ℕ, N ≤ n ∧ C < |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n := by
  by_contra! bounded
  have positiveR : 0 < R := by
    exact_mod_cast (lt_of_le_of_lt (norm_nonneg z) inside)
  have eventual : ∀ᶠ n : ℕ in atTop,
      |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n ≤ C := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact bounded n hn
  have nonzero := canonical_weighted_tail_bound_zero_free R positiveR withinDisk C eventual
    z (by simpa only [Metric.mem_ball, dist_zero_right] using inside)
  exact nonzero zero

/-- The same tail obstruction written for an actual xi zero. The radius test
uses its exact Mobius location, without replacing the zero by its imaginary part. -/
theorem xi_zero_forces_weighted_tail_escape (s : ℂ) (zero : xiReading s = 0)
    (R : ℝ≥0) (inside : ‖1 - s⁻¹‖ < (R : ℝ)) (withinDisk : R ≤ 1)
    (N : ℕ) (C : ℝ) :
    ∃ n : ℕ, N ≤ n ∧ C < |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n := by
  have diskZero : canonicalXiDisk (1 - s⁻¹) = 0 := by
    rw [canonicalXiDisk, show (1 : ℂ) - (1 - s⁻¹) = s⁻¹ by ring, inv_inv]
    exact zero
  exact disk_zero_forces_weighted_tail_escape (1 - s⁻¹) diskZero R inside withinDisk N C

/-- A hypothetical zero of the actual transformed xi function strictly inside
the unit disk yields a rate R<1 at which every exponential envelope fails. -/
theorem disk_zero_forces_exponential_escape (z : ℂ)
    (inDisk : z ∈ Metric.ball (0 : ℂ) 1) (zero : canonicalXiDisk z = 0) :
    ∃ R : ℝ≥0, ‖z‖ < (R : ℝ) ∧ R < 1 ∧
      ∀ N : ℕ, ∀ C : ℝ,
        ∃ n : ℕ, N ≤ n ∧ C < |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n := by
  have hn : ‖z‖₊ < (1 : ℝ≥0) := by
    exact_mod_cast (show ‖z‖ < 1 from by
      simpa only [Metric.mem_ball, dist_zero_right] using inDisk)
  obtain ⟨R, hzR, hR⟩ := exists_between hn
  have inside : ‖z‖ < (R : ℝ) := by exact_mod_cast hzR
  exact ⟨R, inside, hR, fun N C =>
    disk_zero_forces_weighted_tail_escape z zero R inside hR.le N C⟩

/-- RH supplies a bounded weighted coefficient family at EVERY radius below
one. The bound is constructed from the complete absolute coefficient sum. -/
theorem rh_canonical_weighted_envelopes (hRH : RiemannHypothesis)
    (R : ℝ≥0) (hR : R < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n ≤ C := by
  have hs := rh_canonical_li_disk_summable hRH R hR
  refine ⟨∑' n : ℕ, |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n,
    tsum_nonneg (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg R.property n)), ?_⟩
  intro n
  exact hs.le_tsum n (fun j _ => mul_nonneg (abs_nonneg _) (pow_nonneg R.property j))

/-- A weighted bound at R controls absolute convergence at every smaller r.
The comparison keeps the factor (r/R)^n and does not discard absolute values. -/
theorem canonical_smaller_radius_summable (r R : ℝ≥0) (hsmall : r < R)
    (C : ℝ) (bound : ∀ n : ℕ,
      |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n ≤ C) :
    Summable (fun n : ℕ => |canonicalLiCoefficient (n + 1)| * (r : ℝ) ^ n) := by
  have Rpos : (0 : ℝ) < R := lt_of_le_of_lt r.property hsmall
  have ratio_nonneg : 0 ≤ (r : ℝ) / R := div_nonneg r.property Rpos.le
  have ratio_lt : (r : ℝ) / R < 1 := (div_lt_one Rpos).mpr hsmall
  have major := (summable_geometric_of_lt_one ratio_nonneg ratio_lt).mul_left C
  have comparison (n : ℕ) :
      |canonicalLiCoefficient (n + 1)| * (r : ℝ) ^ n ≤ C * ((r : ℝ) / R) ^ n := by
    calc
      _ = (|canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n) * ((r : ℝ) / R) ^ n := by
        rw [div_pow]
        field_simp [ne_of_gt Rpos]
      _ ≤ C * ((r : ℝ) / R) ^ n :=
        mul_le_mul_of_nonneg_right (bound n) (pow_nonneg ratio_nonneg n)
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg r.property n)) comparison major

/-- Exact all-radius envelope criterion for the original canonical sequence.
The equivalent exponential-rate form has quantifiers: for every q>1 there is
one finite C_q controlling every coefficient by C_q*q^n. No uniform C is claimed. -/
theorem rh_iff_canonical_weighted_envelopes :
    RiemannHypothesis ↔ ∀ R : ℝ≥0, R < 1 →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ n : ℕ, |canonicalLiCoefficient (n + 1)| * (R : ℝ) ^ n ≤ C := by
  refine ⟨rh_canonical_weighted_envelopes, ?_⟩
  intro envelopes
  apply canonical_li_disk_summability_implies_rh
  intro r hr
  obtain ⟨R, hrR, hR⟩ := exists_between hr
  obtain ⟨C, _, bound⟩ := envelopes R hR
  exact canonical_smaller_radius_summable r R hrR C bound

#print axioms canonical_weighted_tail_bound_zero_free
#print axioms disk_zero_forces_weighted_tail_escape
#print axioms disk_zero_forces_exponential_escape
#print axioms rh_iff_canonical_weighted_envelopes

end D5.S3.Weil.Probability.CanonicalLiRadiusObstruction
