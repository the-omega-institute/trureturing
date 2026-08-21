/- GID: D5/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/DiscountedPredictionPseudometric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Discounted prediction distance is a bounded pseudometric. -/

import D5.S3.Observer.MetricGeometry.BellmanMaxEquation
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Defs

/- Library-search audit trail (2026-08-21):
   * The canonical source object is the existing
     `D5.S3.Observer.MetricGeometry.BellmanMaxEquation.discountedPredictionDistance`;
     this module imports and reuses it rather than redeclaring a sibling distance.
   * Repository search found the canonical discounted-distance definition and Bellman theorem,
     but no theorem proving its bounded pseudometric laws.
   * Pinned Mathlib exact supporting declarations are `dist_nonneg`, `dist_self`, `dist_comm`,
     `dist_triangle`, `pow_le_one₀`, `le_ciSup`, and `ciSup_le`; no packaged full statement hit.
   * Loogle and LeanSearch exact full-statement searches were misses; the proof uses the
     conditionally complete real supremum API directly. -/

namespace D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric

open D5.S3.Observer.MetricGeometry.BellmanMaxEquation

private theorem discounted_terms_bddAbove
    {Y O : Type*} [PseudoMetricSpace O]
    (update : Y -> Y) (readout : Y -> O) (gamma bound : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1)
    (hbound : ∀ (a b : O), dist a b ≤ bound) (y y' : Y) :
    BddAbove (Set.range fun k : Nat =>
      gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y'))) := by
  refine ⟨bound, ?_⟩
  rintro _ ⟨k, rfl⟩
  calc
    gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
        1 * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) :=
      mul_le_mul_of_nonneg_right
        (pow_le_one₀ hgamma.1.le hgamma.2) (dist_nonneg)
    _ = dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) := one_mul _
    _ ≤ bound := hbound _ _

private theorem discounted_term_nonnegative
    {Y O : Type*} [PseudoMetricSpace O]
    (update : Y -> Y) (readout : Y -> O) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioc 0 1) (y y' : Y) (k : Nat) :
    0 ≤ gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) := by
  exact mul_nonneg (pow_nonneg hgamma.1.le _) (dist_nonneg)

/-- A bounded output pseudometric remains a bounded pseudometric after taking the
discounted supremum over every deterministic update orbit. -/
theorem discounted_prediction_pseudometric
    {Y O : Type*} [PseudoMetricSpace O]
    (update : Y -> Y) (readout : Y -> O)
    (gamma bound : Real) (hgamma : gamma ∈ Set.Ioc 0 1)
    (hbound : ∀ (a b : O), dist a b ≤ bound) :
    ∀ y y' y'' : Y,
      (0 ≤ discountedPredictionDistance update readout dist gamma y y' ∧
        discountedPredictionDistance update readout dist gamma y y' ≤ bound) ∧
      discountedPredictionDistance update readout dist gamma y y = 0 ∧
      discountedPredictionDistance update readout dist gamma y y' =
        discountedPredictionDistance update readout dist gamma y' y ∧
      discountedPredictionDistance update readout dist gamma y y' ≤
        discountedPredictionDistance update readout dist gamma y y'' +
          discountedPredictionDistance update readout dist gamma y'' y' := by
  intro y y' y''
  have hterms := discounted_terms_bddAbove update readout gamma bound hgamma hbound
  have hnonnegative :
      0 ≤ discountedPredictionDistance update readout dist gamma y y' := by
    unfold discountedPredictionDistance
    exact (discounted_term_nonnegative update readout gamma hgamma y y' 0).trans
      (le_ciSup (hterms y y') 0)
  have hbounded :
      discountedPredictionDistance update readout dist gamma y y' ≤ bound := by
    unfold discountedPredictionDistance
    apply ciSup_le
    intro k
    calc
      gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
          1 * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ hgamma.1.le hgamma.2) (dist_nonneg)
      _ = dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) := one_mul _
      _ ≤ bound := hbound _ _
  have hdiagonal :
      discountedPredictionDistance update readout dist gamma y y = 0 := by
    unfold discountedPredictionDistance
    simp [dist_self]
  have hsymmetric :
      discountedPredictionDistance update readout dist gamma y y' =
        discountedPredictionDistance update readout dist gamma y' y := by
    unfold discountedPredictionDistance
    congr 1
    funext k
    rw [dist_comm]
  have htriangle :
      discountedPredictionDistance update readout dist gamma y y' ≤
        discountedPredictionDistance update readout dist gamma y y'' +
          discountedPredictionDistance update readout dist gamma y'' y' := by
    unfold discountedPredictionDistance
    apply ciSup_le
    intro k
    calc
      gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y')) ≤
          gamma ^ k *
            (dist (readout ((update^[k]) y)) (readout ((update^[k]) y'')) +
              dist (readout ((update^[k]) y'')) (readout ((update^[k]) y'))) :=
        mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (pow_nonneg hgamma.1.le _)
      _ = gamma ^ k * dist (readout ((update^[k]) y)) (readout ((update^[k]) y'')) +
          gamma ^ k * dist (readout ((update^[k]) y'')) (readout ((update^[k]) y')) := by
        rw [mul_add]
      _ ≤ (⨆ j : Nat, gamma ^ j *
            dist (readout ((update^[j]) y)) (readout ((update^[j]) y''))) +
          (⨆ j : Nat, gamma ^ j *
            dist (readout ((update^[j]) y'')) (readout ((update^[j]) y'))) :=
        add_le_add (le_ciSup (discounted_terms_bddAbove update readout gamma bound
          hgamma hbound y y'') k)
          (le_ciSup (discounted_terms_bddAbove update readout gamma bound
            hgamma hbound y'' y') k)
  exact ⟨⟨hnonnegative, hbounded⟩, hdiagonal, hsymmetric, htriangle⟩

/-- The output, discount, and bound hypotheses have a checked one-state witness. -/
example : ∃ gamma bound : Real,
    gamma ∈ Set.Ioc 0 1 ∧ (∀ a b : PUnit, dist a b ≤ bound) := by
  refine ⟨(1 : Real) / 2, 0, ?_, ?_⟩
  · constructor <;> norm_num
  · intro a b
    simp

/-- The state domain used by the source definition is inhabited. -/
example : PUnit := PUnit.unit

#print axioms discounted_prediction_pseudometric

end D5.S3.Observer.MetricGeometryLaws.DiscountedPredictionPseudometric
