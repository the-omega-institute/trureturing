/- GID: D5/S3/ConceptDynamics/Completion/TargetClosureReflection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/TargetClosureReflection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target closure is the least target-sufficient refinement of a concept. -/

import D5.S3.ConceptDynamics.Completion.TargetClosureOperator

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'target_closure_reflection_universal' D5 Golden/Frozen/accepted`
     now hits only this candidate module; no pre-existing or accepted duplicate was found.
   * The required `reflection|Suff|closure|universal` repository search found
     `TargetClosureOperator` as the exact upstream closure and join-law source,
     and `UniversalSufficiencyFactorization` as the exact target-sufficiency source.
   * Direct inspection of `ExperimentalQuotientUniversality` found an adjacent
     quotient descent property, not a reflection in the concept refinement order.
   * `targetClosure`, `target_closure_three_laws`, `Refines`, `conceptJoin`,
     `concept_join_universal`, `ConceptEquivalent`, `canonicalTargetReadout`,
     `universal_sufficiency_factorization`, and `refinement_transitive` are reused.
   * No stronger theorem states the requested equivalence. The remaining proof
     only composes refinement witnesses and applies the join universal property. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.TargetClosureReflection

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open D5.S3.ConceptDynamics.Completion.TargetClosureOperator

/-- A concept belongs to `Suff_T` when the canonical target readout factors through it. -/
def TargetSufficient {X D Y : Type*} (q_D : Concept X D) (T : X -> Y) : Prop :=
  Refines (canonicalTargetReadout T) q_D

/-- Membership in `Suff_T` is equivalently constancy of the target on concept fibers. -/
theorem target_sufficient_iff_fiber_constant
    {X D Y : Type*} [Nonempty X] (q_D : Concept X D) (T : X -> Y) :
    TargetSufficient q_D T <->
      forall x y : X, q_D x = q_D y -> T x = T y := by
  simpa only [TargetSufficient] using
    ((universal_sufficiency_factorization q_D T).1.trans
      (universal_sufficiency_factorization q_D T).2)

/-- Target closure has the reflection universal property at every target-sufficient concept. -/
theorem target_closure_reflection_universal
    {X B D Y : Type*} (q_C : Concept X B) (q_D : Concept X D) (T : X -> Y)
    (hD : TargetSufficient q_D T) :
    Refines (targetClosure q_C T) q_D <-> Refines q_C q_D := by
  constructor
  · intro hClosure
    exact refinement_transitive q_C (targetClosure q_C T) q_D hClosure
      (target_closure_three_laws q_C q_D T).1
  · intro hC
    simpa only [targetClosure] using
      (concept_join_universal q_C (canonicalTargetReadout T) q_D).2.2 hC hD

/-- Target closure is the least target-sufficient refinement of the original concept. -/
theorem target_closure_is_least_target_sufficient_refinement
    {X B Y : Type*} (q_C : Concept X B) (T : X -> Y) :
    TargetSufficient (targetClosure q_C T) T /\
      Refines q_C (targetClosure q_C T) /\
      forall {D : Type*} (q_D : Concept X D),
        TargetSufficient q_D T -> Refines q_C q_D ->
          Refines (targetClosure q_C T) q_D := by
  constructor
  · simpa only [TargetSufficient, targetClosure] using
      (concept_join_universal q_C (canonicalTargetReadout T) q_C).2.1
  constructor
  · exact (target_closure_three_laws q_C q_C T).1
  · intro D q_D hD hC
    exact (target_closure_reflection_universal q_C q_D T hD).2 hC

/-- Target closure is target-sufficient and applying completion again changes no distinctions. -/
theorem target_closure_is_target_sufficient_fixed_point
    {X B Y : Type*} (q_C : Concept X B) (T : X -> Y) :
    TargetSufficient (targetClosure q_C T) T /\
      ConceptEquivalent (targetClosure (targetClosure q_C T) T)
        (targetClosure q_C T) := by
  constructor
  · simpa only [TargetSufficient, targetClosure] using
      (concept_join_universal q_C (canonicalTargetReadout T) q_C).2.1
  · exact (target_closure_three_laws q_C q_C T).2.2

/-- Without target sufficiency, a concept can refine `C` without refining its target closure. -/
theorem target_sufficiency_hypothesis_is_necessary :
    exists q_C q_D : Concept Bool Unit,
      Not (TargetSufficient q_D (id : Bool -> Bool)) /\
        Refines q_C q_D /\
        Not (Refines (targetClosure q_C (id : Bool -> Bool)) q_D) := by
  let q : Concept Bool Unit := fun _ => ()
  refine ⟨q, q, ?_, ⟨id, rfl⟩, ?_⟩
  · intro hSufficient
    have hFiber :=
      (target_sufficient_iff_fiber_constant q (id : Bool -> Bool)).1 hSufficient
    exact Bool.false_ne_true (hFiber false true rfl)
  · rintro ⟨factor, hfactor⟩
    have hClosureEqual :
        targetClosure q (id : Bool -> Bool) false =
          targetClosure q (id : Bool -> Bool) true := by
      rw [hfactor]
      rfl
    have hTargetEqual : false = true := by
      have hPairEqual := congrArg
        (fun pair : Unit × TargetImage (id : Bool -> Bool) => pair.2.1)
        hClosureEqual
      simpa only [targetClosure, conceptJoin, canonicalTargetReadout, id_eq] using hPairEqual
    exact Bool.false_ne_true hTargetEqual

example :
    Refines (targetClosure (id : Concept Bool Bool) id) (id : Concept Bool Bool) <->
      Refines (id : Concept Bool Bool) (id : Concept Bool Bool) := by
  apply target_closure_reflection_universal
  exact ⟨fun b => ⟨b, b, rfl⟩, rfl⟩

#print axioms target_closure_reflection_universal

end D5.S3.ConceptDynamics.Completion.TargetClosureReflection
