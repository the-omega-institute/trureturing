/- GID: D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Discounted future distance gives the canonical observer pseudometric geometry. -/

import D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric
import D5.S3.Observer.Separation.FiniteFutureCongruence
import Mathlib.Topology.MetricSpace.Lipschitz

/- Library-search audit trail (2026-09-01):
   * Repository and formalization-receipt searches found the canonical
     `discountedPredictionDistance`, its Bellman equation, and its pseudometric laws, all of
     which are imported and reused here. No declaration combined those laws with the positive
     discount zero kernel or the induced Lipschitz update.
   * The same-section finite-future atoms remain residual-open. Content-based searches found
     only the unweighted dual-supremum kernel and the discount-one bounded-horizon kernel.
   * Pinned Mathlib provides `PseudoMetricSpace`, `LipschitzWith.of_dist_le_mul`,
     `Real.coe_toNNReal`, `le_div_iff₀`, and `dist_eq_zero`; no packaged full statement hit.
   * Loogle returned only generic Lipschitz declarations, LeanSearch's API request failed, and
     the pinned non-Mathlib packages contained no related full theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.CanonicalDiscountedFutureGeometry

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation
open D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric
open D5.S3.Observer.Separation.FiniteFutureCongruence

private theorem prediction_terms_bddAbove
    {Y O : Type*} [PseudoMetricSpace O]
    (update : Y -> Y) (readout : Y -> O) (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hbound : ∀ a b : O, dist a b ≤ bound) (y y' : Y) :
    BddAbove (Set.range fun k : Nat =>
      gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
  refine ⟨bound, ?_⟩
  rintro _ ⟨k, rfl⟩
  calc
    gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
        1 * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) :=
      mul_le_mul_of_nonneg_right
        (pow_le_one₀ hgamma.1.le hgamma.2) dist_nonneg
    _ = dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) := one_mul _
    _ ≤ bound := hbound _ _

/-- The existing discounted prediction distance, equipped with its canonical
pseudometric-space structure. -/
@[reducible]
noncomputable def discountedFuturePseudoMetricSpace
    {Y O : Type*} [PseudoMetricSpace O]
    (update : Y -> Y) (readout : Y -> O) (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hbound : ∀ a b : O, dist a b ≤ bound) : PseudoMetricSpace Y := by
  have laws :=
    discounted_prediction_pseudometric update readout gamma bound hgamma hbound
  exact
    { dist := discountedPredictionDistance update readout dist gamma
      dist_self := fun y => (laws y y y).2.1
      dist_comm := fun y y' => (laws y y' y).2.2.1
      dist_triangle := fun y y' y'' => (laws y y'' y').2.2.2 }

private theorem discounted_prediction_zero_iff_infinite_future
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O) (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hbound : ∀ a b : O, dist a b ≤ bound) (y y' : Y) :
    discountedPredictionDistance update readout dist gamma y y' = 0 ↔
      (y, y') ∈ infiniteFutureRelation update readout := by
  constructor
  · intro hzero
    change ∀ k, readout ((update^[k]) y) = readout ((update^[k]) y')
    intro k
    have hterm_le :
        gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
          discountedPredictionDistance update readout dist gamma y y' := by
      unfold discountedPredictionDistance
      exact le_ciSup
        (prediction_terms_bddAbove update readout gamma bound hgamma hbound y y') k
    have hterm_zero :
        gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) = 0 := by
      apply le_antisymm
      · simpa only [hzero] using hterm_le
      · exact mul_nonneg (pow_nonneg hgamma.1.le _) dist_nonneg
    have hdist_zero :
        dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) = 0 :=
      (mul_eq_zero.mp hterm_zero).resolve_left (ne_of_gt (pow_pos hgamma.1 k))
    exact dist_eq_zero.mp hdist_zero
  · intro hrelation
    change ∀ k, readout ((update^[k]) y) = readout ((update^[k]) y') at hrelation
    unfold discountedPredictionDistance
    simp only [hrelation, dist_self, mul_zero, ciSup_const]

/-- For a strictly discounted bounded observer, the canonical future distance is a
pseudometric dominating present output distance. Updating is `gamma⁻¹`-Lipschitz, and its
zero kernel is exactly equality of every finite future observation. -/
theorem canonical_discounted_future_geometry
    {Y O : Type*} [MetricSpace O]
    (update : Y -> Y) (readout : Y -> O) (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioo 0 1)
    (hbound : ∀ a b : O, dist a b ≤ bound) :
    ∃ metric : PseudoMetricSpace Y,
      (∀ y y', metric.toDist.dist y y' =
        discountedPredictionDistance update readout dist gamma y y') ∧
      (∀ y y', dist (readout y) (readout y') ≤ metric.toDist.dist y y') ∧
      (∀ y y', metric.toDist.dist (update y) (update y') ≤
        gamma⁻¹ * metric.toDist.dist y y') ∧
      (letI := metric; LipschitzWith (Real.toNNReal gamma⁻¹) update) ∧
      ∀ y y', metric.toDist.dist y y' = 0 ↔
        (y, y') ∈ infiniteFutureRelation update readout := by
  have hgammaIoc : gamma ∈ Set.Ioc 0 1 := ⟨hgamma.1, hgamma.2.le⟩
  let metric :=
    discountedFuturePseudoMetricSpace update readout gamma bound hgammaIoc hbound
  have hcurrent : ∀ y y',
      dist (readout y) (readout y') ≤
        discountedPredictionDistance update readout dist gamma y y' := by
    intro y y'
    rw [discounted_prediction_distance_bellman update readout dist gamma bound
      hgammaIoc (fun a b => ⟨dist_nonneg, hbound a b⟩) y y']
    exact le_max_left _ _
  have hcontraction : ∀ y y',
      discountedPredictionDistance update readout dist gamma (update y) (update y') ≤
        gamma⁻¹ * discountedPredictionDistance update readout dist gamma y y' := by
    intro y y'
    have hscaled :
        gamma * discountedPredictionDistance update readout dist gamma (update y) (update y') ≤
          discountedPredictionDistance update readout dist gamma y y' := by
      rw [discounted_prediction_distance_bellman update readout dist gamma bound
        hgammaIoc (fun a b => ⟨dist_nonneg, hbound a b⟩) y y']
      exact le_max_right _ _
    calc
      discountedPredictionDistance update readout dist gamma (update y) (update y') ≤
          discountedPredictionDistance update readout dist gamma y y' / gamma :=
        (le_div_iff₀ hgamma.1).2 (by simpa only [mul_comm] using hscaled)
      _ = gamma⁻¹ * discountedPredictionDistance update readout dist gamma y y' := by
        rw [div_eq_mul_inv, mul_comm]
  refine ⟨metric, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y'
    rfl
  · intro y y'
    exact hcurrent y y'
  · intro y y'
    exact hcontraction y y'
  · letI : PseudoMetricSpace Y := metric
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hgamma.1.le)]
    exact hcontraction y y'
  · intro y y'
    exact discounted_prediction_zero_iff_infinite_future update readout gamma bound
      hgammaIoc hbound y y'

#print axioms canonical_discounted_future_geometry

end D5.S3.Observer.MetricGeometryLaws.CanonicalDiscountedFutureGeometry
