/- GID: D5/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/EvaluationSupremumMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluation suprema are least among pseudometrics dominating every readout. -/

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/- Library-search audit trail (2026-08-28):
   * Repository searches for evaluation-distance suprema, least dominating
     pseudometrics, and one-Lipschitz readouts found no exact D5 theorem.
   * Pinned Mathlib has function-space supremum distance identities, including
     `PiLp.dist_eq_iSup` and `ContinuousMap.dist_eq_iSup`, but neither states the
     source's paired state/protocol minimality theorem.
   * The exact supporting lattice declaration `ciSup_le` is applied to each
     canonical evaluation supremum below. No source object is redeclared. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.MetricGeometryLaws.EvaluationSupremumMinimality

/-- The state and protocol evaluation suprema are pointwise below every
pseudometric that dominates all corresponding evaluation distances. -/
theorem evaluation_suprema_are_least_dominating
    {X P Lambda : Type*} [PseudoMetricSpace Lambda]
    (evaluation : X -> P -> Lambda)
    (stateCompetitor : PseudoMetricSpace X)
    (protocolCompetitor : PseudoMetricSpace P) :
    ((forall x y : X, forall p : P,
        dist (evaluation x p) (evaluation y p) <=
          @dist X stateCompetitor.toDist x y) ->
      forall x y : X,
        (⨆ p : P, dist (evaluation x p) (evaluation y p)) <=
          @dist X stateCompetitor.toDist x y) ∧
    ((forall p q : P, forall x : X,
        dist (evaluation x p) (evaluation x q) <=
          @dist P protocolCompetitor.toDist p q) ->
      forall p q : P,
        (⨆ x : X, dist (evaluation x p) (evaluation x q)) <=
          @dist P protocolCompetitor.toDist p q) := by
  constructor
  · intro hdominates x y
    cases isEmpty_or_nonempty P with
    | inl hempty =>
        letI : IsEmpty P := hempty
        letI : PseudoMetricSpace X := stateCompetitor
        rw [iSup_of_empty', Real.sSup_empty]
        exact dist_nonneg
    | inr hnonempty =>
        letI : Nonempty P := hnonempty
        exact ciSup_le fun p => hdominates x y p
  · intro hdominates p q
    cases isEmpty_or_nonempty X with
    | inl hempty =>
        letI : IsEmpty X := hempty
        letI : PseudoMetricSpace P := protocolCompetitor
        rw [iSup_of_empty', Real.sSup_empty]
        exact dist_nonneg
    | inr hnonempty =>
        letI : Nonempty X := hnonempty
        exact ciSup_le fun x => hdominates p q x

#print axioms evaluation_suprema_are_least_dominating

end D5.S3.Observer.MetricGeometryLaws.EvaluationSupremumMinimality
