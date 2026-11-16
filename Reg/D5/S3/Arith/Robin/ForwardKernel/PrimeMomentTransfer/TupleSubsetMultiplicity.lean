import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity

open _root_.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v

/-- Cardinality observes the finite set of admissible tuples over its original carriers. -/
abbrev signature : Signature where
  Params := Σ ι : Type u, Type v
  State p := Finset (p.1 → p.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ A => A.card) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (S : Finset α) (R : Finset ι) (v : ι → α),
    r.readout () ⟨ι, α⟩ ((Fintype.piFinset (fun _ : ι => S)).filter
      (fun d => ∀ i ∈ R, d i = v i)) ≤ S.card ^ (Fintype.card ι - R.card)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hh := @h (ULift.{u} Unit) (ULift.{v} Unit) inferInstance inferInstance inferInstance
    {ULift.up ()} ∅ (fun _ => ULift.up ())
  norm_num [rejected, realize] at hh

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit⟩, ∅, {fun _ => ULift.up ()}, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u,v} (type_of% @forced_tuple_card_le.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨forced_tuple_card_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@forced_tuple_card_le.{u,v}) (Realization signature.{u,v}) Unit Unit where
  unitName := `D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity.forced_tuple_card_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨source_registration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity
