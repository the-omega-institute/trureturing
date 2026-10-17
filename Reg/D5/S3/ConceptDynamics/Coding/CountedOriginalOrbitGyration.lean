import D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration
open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
noncomputable section

abbrev cardinalSignature : Signature where
  Params := Σ' _n : ℕ, Σ' d : ℕ, NeZero d
  State p := CountMat p.1 p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def cardinalActual : Realization cardinalSignature :=
  realize cardinalSignature (fun _ p A =>
    letI : NeZero p.2.1 := p.2.2
    Fintype.card (PrimitivePath A p.2.1)) (fun e => nomatch e)

def cardinalRejected : Realization cardinalSignature :=
  realize cardinalSignature (fun _ p A => cardinalActual.readout () p A + 1)
    (fun e => nomatch e)

def cardinalArena : Arena where
  signature := cardinalSignature
  Law r := ∀ {n : ℕ} (A : CountMat n n) (d : ℕ) [h : NeZero d],
    r.readout () ⟨n, d, h⟩ A = d * Fintype.card (ActualPathOrbit A d)

private theorem cardinal_actual_law : cardinalArena.Law cardinalActual := by
  intro n A d h
  exact primitivePath_card_eq_period_mul_orbit_card A d

private theorem cardinal_rejected_law : ¬ cardinalArena.Law cardinalRejected := by
  intro h
  let A : CountMat 0 0 := fun _ _ => 0
  have he := h A 1
  have ha := primitivePath_card_eq_period_mul_orbit_card A 1
  change Fintype.card (PrimitivePath A 1) + 1 = _ at he
  omega

private theorem cardinal_dependence : ObservationalDependence cardinalSignature cardinalActual := by
  intro i
  cases i
  let A₀ : CountMat 1 1 := fun _ _ => 0
  let A₁ : CountMat 1 1 := fun _ _ => 1
  haveI : IsEmpty (PrimitivePath A₀ 1) :=
    ⟨fun x => Fin.elim0 (x.val.val 0).number⟩
  let a : LegalWord A₁ 1 := ⟨fun _ => ⟨0, 0, 0⟩, fun _ => rfl⟩
  have ha : Primitive a.val := by
    intro k hk
    exact (hk (Subsingleton.elim _ _)).elim
  have hp : 0 < Fintype.card (PrimitivePath A₁ 1) :=
    Fintype.card_pos_iff.mpr ⟨primitiveWordEquiv A₁ ⟨a, ha⟩⟩
  refine ⟨⟨1, 1, inferInstance⟩, A₀, A₁, ?_⟩
  change Fintype.card (PrimitivePath A₀ 1) ≠ Fintype.card (PrimitivePath A₁ 1)
  rw [Fintype.card_eq_zero]
  exact (Nat.ne_of_gt hp).symm

def cardinalRegistration : Registration cardinalArena
    (∀ {n : ℕ} (A : CountMat n n) (d : ℕ) [NeZero d],
      Fintype.card (PrimitivePath A d) = d * Fintype.card (ActualPathOrbit A d)) where
  actual := cardinalActual
  bridge := Iff.rfl
  variation := ⟨cardinal_actual_law, cardinalRejected, cardinal_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cardinalRejected, ?_, rfl, cardinal_rejected_law⟩
      intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro i
      exact nomatch i
  dependence := cardinal_dependence

def registration_cardinal : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.ConceptDynamics.Coding.CountedOrderTypeGyration.primitivePath_card_eq_period_mul_orbit_card)
    (type_of% (realize cardinalSignature (fun _ p A =>
      letI : NeZero p.2.1 := p.2.2
      Fintype.card (PrimitivePath A p.2.1)) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration.cardinal
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration.cardinalRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨cardinalArena⟩
  objectArena := .source ⟨cardinalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cardinalArena ⟨cardinalRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardinalSignature (fun _ p A =>
    letI : NeZero p.2.1 := p.2.2
    Fintype.card (PrimitivePath A p.2.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Coding.CountedOriginalOrbitGyration

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
