/- GID: D5/S3/ConceptDynamics/Topology/CompactClassificationPositiveMargin
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/CompactClassificationPositiveMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact discrete classification has an attained positive class margin. -/

import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-08-26):
   * Searches across D5 for compact classifiers, positive margins, cross-class
     distances, and intersecting fiber closures found no exact whole theorem.
     `ContinuousHardClassificationObstruction` is adjacent but concerns connected
     domains and constancy rather than a compact metric margin.
   * Pinned Mathlib exact supporting hits are `IsCompact.image`,
     `IsCompact.isLeast_sInf`, `continuous_dist`, and `isClosed_discrete`.
     Mathlib has point-to-set `Metric.infDist` but no exact set-to-set theorem
     packaging the source's minimum and closure obstruction.
   * No new `def` or `abbrev` is introduced. The public local objects are formed
     directly from the classifier, product projections, `dist`, set image, and
     `sInf`, so there is no family primitive fork. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Topology.CompactClassificationPositiveMargin

/-- A nonconstant continuous classifier from a compact metric space to a discrete
space has an attained positive minimum among all cross-class distances. Distances
below that minimum cannot cross a class boundary. Independently, intersecting
closures of two distinct fibers obstruct continuity.

The nonconstancy premise is local to the positive-margin half: without two attained
classes the real-valued minimum displayed in the source is indexed by the empty set. -/
theorem compact_classification_positive_margin_and_closure_obstruction
    {X Y : Type*} [MetricSpace X] [CompactSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (classifier : X -> Y) :
    ((Continuous classifier ∧
        ∃ first second : X, classifier first ≠ classifier second) ->
      let separatedPairs : Set (X × X) :=
        {pair | classifier pair.1 ≠ classifier pair.2}
      let crossClassDistances : Set ℝ :=
        (fun pair : X × X => dist pair.1 pair.2) '' separatedPairs
      let margin : ℝ := sInf crossClassDistances
      0 < margin ∧
        margin ∈ crossClassDistances ∧
        ∀ first second : X,
          dist first second < margin -> classifier first = classifier second) ∧
    ((∃ firstLabel secondLabel : Y,
        firstLabel ≠ secondLabel ∧
          (closure (classifier ⁻¹' {firstLabel}) ∩
            closure (classifier ⁻¹' {secondLabel})).Nonempty) ->
      ¬Continuous classifier) := by
  constructor
  · rintro ⟨classifierContinuous, ⟨first, second, labelsDiffer⟩⟩
    let separatedPairs : Set (X × X) :=
      {pair | classifier pair.1 ≠ classifier pair.2}
    let crossClassDistances : Set ℝ :=
      (fun pair : X × X => dist pair.1 pair.2) '' separatedPairs
    change 0 < sInf crossClassDistances ∧
      sInf crossClassDistances ∈ crossClassDistances ∧
      ∀ left right : X,
        dist left right < sInf crossClassDistances -> classifier left = classifier right
    have pairClassifierContinuous :
        Continuous (fun pair : X × X =>
          (classifier pair.1, classifier pair.2)) :=
      (classifierContinuous.comp continuous_fst).prodMk
        (classifierContinuous.comp continuous_snd)
    have separatedPairsClosed : IsClosed separatedPairs := by
      change IsClosed
        ((fun pair : X × X => (classifier pair.1, classifier pair.2)) ⁻¹'
          {outputs : Y × Y | outputs.1 ≠ outputs.2})
      exact (isClosed_discrete _).preimage pairClassifierContinuous
    have separatedPairsCompact : IsCompact separatedPairs :=
      separatedPairsClosed.isCompact
    have crossClassDistancesCompact : IsCompact crossClassDistances :=
      separatedPairsCompact.image continuous_dist
    have crossClassDistancesNonempty : crossClassDistances.Nonempty := by
      refine ⟨dist first second, ⟨(first, second), ?_, rfl⟩⟩
      exact labelsDiffer
    have marginLeast : IsLeast crossClassDistances (sInf crossClassDistances) :=
      crossClassDistancesCompact.isLeast_sInf crossClassDistancesNonempty
    have marginPositive : 0 < sInf crossClassDistances := by
      rcases marginLeast.1 with ⟨pair, pairSeparated, pairDistance⟩
      rw [← pairDistance]
      exact dist_pos.mpr fun pointsEqual =>
        pairSeparated (congrArg classifier pointsEqual)
    refine ⟨marginPositive, marginLeast.1, ?_⟩
    intro left right distanceBelowMargin
    by_contra labelsDiffer
    have distanceMember : dist left right ∈ crossClassDistances := by
      refine ⟨(left, right), ?_, rfl⟩
      exact labelsDiffer
    exact (not_lt_of_ge (marginLeast.2 distanceMember)) distanceBelowMargin
  · rintro ⟨firstLabel, secondLabel, labelsDiffer,
      ⟨boundaryPoint, firstClosure, secondClosure⟩⟩ classifierContinuous
    have firstFiberClosed : IsClosed (classifier ⁻¹' {firstLabel}) :=
      (isClosed_discrete _).preimage classifierContinuous
    have secondFiberClosed : IsClosed (classifier ⁻¹' {secondLabel}) :=
      (isClosed_discrete _).preimage classifierContinuous
    have firstValue : classifier boundaryPoint = firstLabel := by
      have boundaryInFiber : boundaryPoint ∈ classifier ⁻¹' {firstLabel} := by
        rw [← firstFiberClosed.closure_eq]
        exact firstClosure
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using boundaryInFiber
    have secondValue : classifier boundaryPoint = secondLabel := by
      have boundaryInFiber : boundaryPoint ∈ classifier ⁻¹' {secondLabel} := by
        rw [← secondFiberClosed.closure_eq]
        exact secondClosure
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using boundaryInFiber
    exact labelsDiffer (firstValue.symm.trans secondValue)

/-- A finite discrete classifier supplies a concrete inhabited domain and a
nonconstant premise for the positive-margin half. -/
example :
    Continuous (id : Bool -> Bool) ∧
      ∃ first second : Bool, id first ≠ id second := by
  exact ⟨continuous_id, ⟨false, true, Bool.false_ne_true⟩⟩

#print axioms compact_classification_positive_margin_and_closure_obstruction

end D5.S3.ConceptDynamics.Topology.CompactClassificationPositiveMargin
