import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration

open _root_.D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Observe fixed-period cardinality while varying the self-map on its original carrier. -/
abbrev periodicSignature : Signature where
  Params := Σ _ : Type u, ℕ
  State p := p.1 → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def periodicActual : Realization periodicSignature.{u} :=
  realize periodicSignature (fun _ p f =>
    Nat.card {x : p.1 // Function.IsPeriodicPt f p.2 x}) (fun e => nomatch e)

def periodicRejected : Realization periodicSignature.{u} :=
  realize periodicSignature (fun _ p f =>
    Nat.card {x : p.1 // Function.IsPeriodicPt f p.2 x} + 1) (fun e => nomatch e)

/-- The original telescope, including positivity and only fixed-period finiteness. -/
abbrev periodicArena : Arena where
  signature := periodicSignature.{u}
  Law r := ∀ {α : Type u} (f : α → α) (n : ℕ) (_hn : 0 < n)
    [Finite {x : α // Function.IsPeriodicPt f n x}],
    r.readout () ⟨α, n⟩ f =
      ∑ d ∈ n.divisors, Nat.card {x : α // Function.minimalPeriod f x = d}

theorem periodic_rejected_law : ¬ periodicArena.{u}.Law periodicRejected := by
  intro h
  have hb := @h (ULift.{u} Empty) id 1 (by decide) inferInstance
  have ha := periodic_card_eq_sum_minimalPeriod (id : ULift.{u} Empty → _) 1 (by decide)
  change Nat.card {x : ULift.{u} Empty // Function.IsPeriodicPt id 1 x} + 1 = _ at hb
  omega

theorem periodic_dependence : ObservationalDependence periodicSignature.{u}
    periodicActual := by
  intro i
  let flip : ULift.{u} Bool → ULift.{u} Bool := fun x => ⟨!x.down⟩
  refine ⟨⟨ULift.{u} Bool, 1⟩, id, flip, ?_⟩
  haveI : IsEmpty {x : ULift.{u} Bool // Function.IsPeriodicPt flip 1 x} := ⟨by
    intro x
    have h := congrArg ULift.down x.property
    cases hx : x.val.down <;>
      simp [Function.IsPeriodicPt, Function.IsFixedPt, flip, hx] at h⟩
  change Nat.card {x : ULift.{u} Bool // Function.IsPeriodicPt id 1 x} ≠
    Nat.card {x : ULift.{u} Bool // Function.IsPeriodicPt flip 1 x}
  rw [Nat.card_of_isEmpty (α :=
    {x : ULift.{u} Bool // Function.IsPeriodicPt flip 1 x})]
  exact Nat.card_ne_zero.mpr ⟨⟨⟨⟨false⟩, Function.is_periodic_id 1 _⟩⟩, inferInstance⟩

def periodicSource : Registration periodicArena.{u}
    (type_of% (@periodic_card_eq_sum_minimalPeriod.{u})) where
  actual := periodicActual
  bridge := Iff.rfl
  variation := ⟨periodic_card_eq_sum_minimalPeriod, periodicRejected, periodic_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨periodicRejected, ?_, rfl, periodic_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := periodic_dependence

def registration_periodic :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@periodic_card_eq_sum_minimalPeriod.{u})
      (Realization periodicSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration.periodic
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration.periodicSource
  realizationSource := none
  generated := false
  arena := .source ⟨periodicArena.{u}⟩
  objectArena := .source ⟨periodicArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source periodicArena.{u} ⟨periodicSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize periodicSignature.{u} (fun _ p f =>
    Nat.card {x : p.1 // Function.IsPeriodicPt f p.2 x}) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms periodic_card_eq_sum_minimalPeriod
#print axioms periodicSource
#print axioms registration_periodic

end
end Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
