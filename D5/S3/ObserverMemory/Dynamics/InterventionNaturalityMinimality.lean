/- GID: D5/S3/ObserverMemory/Dynamics/InterventionNaturalityMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/InterventionNaturalityMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Naturality on singleton addresses forces the minimal controlled quotient factor. -/

import D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality
import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/- Library-search audit trail (2026-08-17):
   * Repository search found `coordinate_restriction_naturality`, which states the forward
     diagonal identity, but no converse extracting transition commutation from all tables.
   * Pinned Mathlib and Loogle found the exact equivalence
     `Function.semiconj_iff_comp_eq`; it is applied below after specializing to `Unit`.
   * Repository search found the exact quotient factorization result
     `controlled_behavior_universal_property`; it is imported and applied directly below.
   * Adjacent pinned-Mathlib quotient hits included `Setoid.quotientKerEquivRange`,
     `Setoid.map_of_le`, and `Setoid.lift_unique`; none packages this combined converse.
   * LeanSearch's shaped web query was unavailable, returning HTTP 404. -/

namespace D5.S3.ObserverMemory.Dynamics.InterventionNaturalityMinimality

universe uA

open D5.S0.Diagonal
open D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- If every nonempty-address diagonal commutes with a surjective controlled realization,
then all of its transitions commute and it maps uniquely onto the complete behavior quotient. -/
theorem intervention_naturality_minimality
    {Y U O W : Type*} [Finite Y] [Finite W]
    (update : U -> Y -> Y) (readout : Y -> O)
    (realization : Y -> W) (realizedUpdate : U -> W -> W)
    (realizedReadout : W -> O)
    (realization_surjective : Function.Surjective realization)
    (readouts_commute : readout = realizedReadout ∘ realization)
    (diagonals_commute : forall (u : U) (A : Type uA) [Nonempty A]
      (table : A -> A -> Y),
      restrictVector (Function.Embedding.refl A) realization
          (EscapeCount.diagonal (update u) table) =
        EscapeCount.diagonal (realizedUpdate u)
          (restrictTable (Function.Embedding.refl A) realization table)) :
    (forall u, realization ∘ update u = realizedUpdate u ∘ realization) /\
      ExistsUnique fun factor : W -> ControlledCompletion update readout =>
        Function.Surjective factor /\
          completionProjection update readout = factor ∘ realization /\
          (forall u, factor ∘ realizedUpdate u =
            completionUpdate update readout u ∘ factor) /\
          completionReadout update readout ∘ factor = realizedReadout := by
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Fintype W := Fintype.ofFinite W
  have updates_commute : forall u,
      realization ∘ update u = realizedUpdate u ∘ realization := by
    intro u
    apply Function.semiconj_iff_comp_eq.mp
    intro y
    let singleton : ULift.{uA} Unit := ULift.up ()
    have hsingleton := congrFun
      (diagonals_commute u (ULift.{uA} Unit) (fun _ _ => y)) singleton
    simpa [restrictVector, restrictTable, EscapeCount.diagonal] using hsingleton
  refine ⟨updates_commute, ?_⟩
  exact (controlled_behavior_universal_property update readout realization
    realizedUpdate realizedReadout realization_surjective updates_commute
    readouts_commute).1

#print axioms intervention_naturality_minimality

end D5.S3.ObserverMemory.Dynamics.InterventionNaturalityMinimality
