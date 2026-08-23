/- GID: D5/S3/ConceptDynamics/Completion/TargetClosureOperator
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/TargetClosureOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joining with the canonical target readout obeys the three closure laws. -/

import D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'target_closure_three_laws' D5 Golden/Frozen/accepted` found no
     repository declaration or accepted duplicate.
   * The required `closure|Closure|cl_T|completion` search found only adjacent
     uses. Direct inspection confirmed that `EmergencyEvidenceNecessity`,
     `ConceptKernelOrderDuality`, and `FutureObligationIncompleteness` do not
     state target closure laws.
   * Exact repository hits `Concept`, `Refines`, `conceptJoin`,
     `concept_join_universal`, `ConceptEquivalent`, `TargetImage`, and
     `canonicalTargetReadout` are imported and reused below.
   * Pinned Mathlib defines `ClosureOperator` for an endomap on one preorder and
     requires literal idempotence. Here a join changes the readout coordinate
     type, so iteration is idempotent only up to `ConceptEquivalent`; forcing a
     Mathlib instance would therefore distort the source statement.
   * No stronger closure theorem was found. The remaining proof uses the join
     universal property with product projections, pairing, and associating a
     repeated target coordinate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.TargetClosureOperator

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- Completion at `T` joins a concept readout with the canonical target readout. -/
def targetClosure {X B Y : Type*} (q_C : Concept X B) (T : X -> Y) :
    Concept X (B × TargetImage T) :=
  conceptJoin q_C (canonicalTargetReadout T)

/-- Target completion is extensive, monotone, and idempotent up to mutual refinement. -/
theorem target_closure_three_laws
    {X B D Y : Type*} (q_C : Concept X B) (q_D : Concept X D) (T : X -> Y) :
    Refines q_C (targetClosure q_C T) ∧
      (Refines q_C q_D -> Refines (targetClosure q_C T) (targetClosure q_D T)) ∧
      ConceptEquivalent (targetClosure (targetClosure q_C T) T)
        (targetClosure q_C T) := by
  constructor
  · simpa [targetClosure] using
      (concept_join_universal q_C (canonicalTargetReadout T) q_C).1
  constructor
  · rintro ⟨factor, hfactor⟩
    refine ⟨fun pair => (factor pair.1, pair.2), ?_⟩
    funext x
    change (q_C x, canonicalTargetReadout T x) =
      (factor (q_D x), canonicalTargetReadout T x)
    rw [hfactor]
    rfl
  · constructor
    · exact ⟨fun pair => (pair, pair.2), rfl⟩
    · exact ⟨Prod.fst, rfl⟩

/-- A concept is fixed by target completion exactly when it already refines the target. -/
theorem target_closure_equivalent_iff_target_sufficient
    {X B Y : Type*} (q_C : Concept X B) (T : X -> Y) :
    ConceptEquivalent (targetClosure q_C T) q_C ↔
      Refines (canonicalTargetReadout T) q_C := by
  constructor
  · intro hfixed
    have htargetJoin :
        Refines (canonicalTargetReadout T) (targetClosure q_C T) := by
      simpa [targetClosure] using
        (concept_join_universal q_C (canonicalTargetReadout T) q_C).2.1
    exact refinement_transitive (canonicalTargetReadout T)
      (targetClosure q_C T) q_C hfixed.1 htargetJoin
  · intro htarget
    constructor
    · simpa [targetClosure] using
        (concept_join_universal q_C (canonicalTargetReadout T) q_C).2.2
          (show Refines q_C q_C from ⟨id, rfl⟩) htarget
    · simpa [targetClosure] using
        (concept_join_universal q_C (canonicalTargetReadout T) q_C).1

example :
    ConceptEquivalent
      (targetClosure (targetClosure (id : Concept Bool Bool) id) id)
      (targetClosure (id : Concept Bool Bool) id) := by
  exact
    (target_closure_three_laws (id : Concept Bool Bool)
      (id : Concept Bool Bool) id).2.2

#print axioms target_closure_three_laws

end D5.S3.ConceptDynamics.Completion.TargetClosureOperator
