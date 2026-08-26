/- GID: D5/S3/ConceptDynamics/Completion/TargetSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/TargetSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three sufficiency criteria agree; empty and singleton cases are audited. -/

import D5.S3.ConceptDynamics.Completion.TargetClosureOperator
import D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion

/- Library-search audit trail (2026-08-25):
   * Exact hit `target_closure_equivalent_iff_target_sufficient` is imported and
     reused for the residual-empty/fixed-point bridge and the packaged theorem.
   * Exact hit `target_recovery_criterion` packages arbitrary-codomain factorization
     and residual emptiness under `Nonempty X`; both clauses are reused below.
   * `directly_provable_laws` also contains the residual/fiber equivalence inside a
     larger conjunction. The narrower recovery criterion is the direct reusable hit.
   * Pinned Mathlib hit `Function.factorsThrough_iff` supplies the third condition.
     It totalizes the decoder outside `Set.range q` using `Classical.choice`.
   * `QueryFamilyIdentification` uses `Quotient.lift` without choice, but factors
     through a quotient projection rather than the raw codomain of the single `q`.
   * Exact hit `defectRelation` has the requested set body and is reused by a thin
     source-facing alias. `targetResidualEntropy` is instead a real-valued entropy.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.TargetSufficiency

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Completion.TargetClosureOperator

/-- The source theorem writes `TargetRes(q, t)` without defining it. This module
supplies the target residual as the pairs that `q` identifies but `t` separates:
`{(x, y) | q x = q y and t x != t y}`. The body reuses the repository's canonical
`defectRelation`. This set is not `targetResidualEntropy`, which is a real number;
the set and entropy are different objects and cannot be interchanged. -/
def targetResidual {X B Y : Type*} (q : Concept X B) (t : X -> Y) : Set (X × X) :=
  defectRelation q t

/-- On inhabited states, residual emptiness is exactly invariance under target closure. -/
theorem target_residual_empty_iff_target_closure_fixed
    {X B Y : Type*} [Nonempty X] (q : Concept X B) (t : X -> Y) :
    targetResidual q t = ∅ <->
      ConceptEquivalent (targetClosure q t) q := by
  have residualIffFiber :
      targetResidual q t = ∅ <->
        forall x y : X, q x = q y -> t x = t y := by
    simpa only [targetResidual] using
      (target_recovery_criterion q t).2.1.symm
  have sufficientIffFiber :
      Refines (canonicalTargetReadout t) q <->
        forall x y : X, q x = q y -> t x = t y :=
    (universal_sufficiency_factorization q t).1.trans
      (universal_sufficiency_factorization q t).2
  exact residualIffFiber.trans
    (sufficientIffFiber.symm.trans
      (target_closure_equivalent_iff_target_sufficient q t).symm)
#print axioms target_residual_empty_iff_target_closure_fixed

/-- Target residual emptiness, constancy on local fibers, and a total target decoder
through the single readout `q` are equivalent. `Nonempty Y` supplies the off-range
decoder value; no finiteness, decidable equality, or algebraic structure is assumed. -/
theorem target_sufficiency_three_way
    {X B Y : Type*} [Nonempty Y] (q : Concept X B) (t : X -> Y) :
    (targetResidual q t = ∅ <->
      forall x y : X, q x = q y -> t x = t y) /\
    ((forall x y : X, q x = q y -> t x = t y) <->
      exists factor : B -> Y, t = factor ∘ q) := by
  have residualIffFiber :
      targetResidual q t = ∅ <->
        forall x y : X, q x = q y -> t x = t y := by
    classical
    cases isEmpty_or_nonempty X with
    | inl stateEmpty =>
        letI : IsEmpty X := stateEmpty
        constructor
        · intro _ x
          exact isEmptyElim x
        · intro _
          ext pair
          exact isEmptyElim pair.1
    | inr stateNonempty =>
        letI : Nonempty X := stateNonempty
        exact (target_residual_empty_iff_target_closure_fixed q t).trans
          ((target_closure_equivalent_iff_target_sufficient q t).trans
            ((universal_sufficiency_factorization q t).1.trans
              (universal_sufficiency_factorization q t).2))
  have fiberIffFactor :
      (forall x y : X, q x = q y -> t x = t y) <->
        exists factor : B -> Y, t = factor ∘ q := by
    simpa only [Function.FactorsThrough] using
      (Function.factorsThrough_iff (f := q) t)
  exact ⟨residualIffFiber, fiberIffFactor⟩
#print axioms target_sufficiency_three_way

/-- Empty states show that the inhabited-state hypothesis on the closure bridge
cannot simply be deleted: the residual is empty, but no total reverse refinement
can map the realized `Unit` coordinate into the empty target image. -/
theorem nonempty_state_hypothesis_is_necessary :
    let q : Concept Empty Unit := fun x => x.elim
    let t : Empty -> Empty := fun x => x.elim
    targetResidual q t = ∅ /\
      Not (ConceptEquivalent (targetClosure q t) q) := by
  dsimp only
  constructor
  · ext pair
    exact pair.1.elim
  · rintro ⟨⟨factor, _⟩, _⟩
    rcases (factor ()).2.property with ⟨state, _⟩
    exact state.elim
#print axioms nonempty_state_hypothesis_is_necessary

/-- Empty states with a nonempty observation type and empty target type show that
fiber constancy alone does not produce a total decoder without target inhabitedness. -/
theorem nonempty_target_hypothesis_is_necessary :
    let q : Concept Empty Unit := fun x => x.elim
    let t : Empty -> Empty := fun x => x.elim
    targetResidual q t = ∅ /\
      (forall x y : Empty, q x = q y -> t x = t y) /\
      Not (Exists fun factor : Unit -> Empty => t = factor ∘ q) := by
  dsimp only
  constructor
  · ext pair
    exact pair.1.elim
  constructor
  · intro x
    exact x.elim
  · rintro ⟨factor, _⟩
    exact (factor ()).elim
#print axioms nonempty_target_hypothesis_is_necessary

/- Degenerate audit: a constant target makes all three conditions true. -/
example {X B Y : Type*} (q : Concept X B) (value : Y) :
    targetResidual q (fun _ => value) = ∅ /\
      (forall x y, q x = q y -> (fun _ : X => value) x = (fun _ => value) y) /\
      exists factor : B -> Y, (fun _ : X => value) = factor ∘ q := by
  constructor
  · ext pair
    simp [targetResidual, defectRelation]
  constructor
  · simp
  · exact ⟨fun _ => value, rfl⟩

/- Degenerate audit: an injective readout, including identity, makes all conditions true. -/
example {X B Y : Type*} [Nonempty Y]
    (q : Concept X B) (t : X -> Y) (hq : Function.Injective q) :
    targetResidual q t = ∅ /\
      (forall x y, q x = q y -> t x = t y) /\
      exists factor : B -> Y, t = factor ∘ q := by
  have fiberConstant : forall x y : X, q x = q y -> t x = t y := by
    intro x y hxy
    exact congrArg t (hq hxy)
  have criteria := target_sufficiency_three_way q t
  exact ⟨criteria.1.mpr fiberConstant, fiberConstant, criteria.2.mp fiberConstant⟩

/- Degenerate audit: a constant readout and nonconstant target make all conditions false. -/
example :
    (targetResidual (fun _ : Bool => ()) (id : Bool -> Bool)).Nonempty /\
      Not (forall x y : Bool, () = () -> id x = id y) /\
      Not (Exists fun factor : Unit -> Bool =>
        (id : Bool -> Bool) = factor ∘ (fun _ : Bool => ())) := by
  have notFiber : Not (forall x y : Bool, () = () -> id x = id y) := by
    intro fiberConstant
    exact Bool.false_ne_true (fiberConstant false true rfl)
  have criteria :=
    target_sufficiency_three_way (fun _ : Bool => ()) (id : Bool -> Bool)
  refine ⟨⟨(false, true), ?_⟩, notFiber, ?_⟩
  · exact ⟨rfl, Bool.false_ne_true⟩
  · intro factorization
    exact notFiber (criteria.2.mpr factorization)

/- Degenerate audit: every readout and target on the singleton state type satisfy all clauses. -/
example {B Y : Type*} (q : Concept Unit B) (t : Unit -> Y) :
    targetResidual q t = ∅ /\
      (forall x y, q x = q y -> t x = t y) /\
      exists factor : B -> Y, t = factor ∘ q := by
  have fiberConstant : forall x y : Unit, q x = q y -> t x = t y := by
    intro x y _
    exact congrArg t (Subsingleton.elim x y)
  letI : Nonempty Y := ⟨t ()⟩
  have criteria := target_sufficiency_three_way q t
  exact ⟨criteria.1.mpr fiberConstant, fiberConstant, criteria.2.mp fiberConstant⟩

end D5.S3.ConceptDynamics.Completion.TargetSufficiency
