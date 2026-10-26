import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
import Reg.Support.DependentFamily

/-! Source-bound audit of the trace of the tensor-factor swap. -/

namespace Reg.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone

open _root_.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

/-- Retain the carrier and its finite enumeration and equality dictionary. -/
abbrev signature : Signature where
  Params := Unit
  State _ := Σ n : Type u, Σ _ : Fintype n, DecidableEq n
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ p =>
    letI : Fintype p.1 := p.2.1
    letI : DecidableEq p.1 := p.2.2
    Matrix.trace (Equiv.Perm.permMatrix ℂ (Equiv.prodComm p.1 p.1)))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The trace identity keeps the complete polymorphic telescope. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {n : Type u} [ft : Fintype n] [de : DecidableEq n],
    r.readout () () ⟨n, ft, de⟩ = (Fintype.card n : ℂ)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} (Fin 1)) inferInstance inferInstance
  change (0 : ℂ) = (Fintype.card (ULift.{u} (Fin 1)) : ℂ) at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), ⟨ULift.{u} (Fin 0), inferInstance, inferInstance⟩,
    ⟨ULift.{u} (Fin 1), inferInstance, inferInstance⟩, ?_⟩
  change Matrix.trace (Equiv.Perm.permMatrix ℂ
    (Equiv.prodComm (ULift.{u} (Fin 0)) (ULift.{u} (Fin 0)))) ≠
    Matrix.trace (Equiv.Perm.permMatrix ℂ
      (Equiv.prodComm (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1))))
  rw [traceSwap, traceSwap]
  norm_num

def source_registration : Registration arena.{u} (type_of% @traceSwap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@traceSwap, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.traceSwap.{u})
      (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.traceSwap.unit
  realizationName :=
    `Reg.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ p =>
    letI : Fintype p.1 := p.2.1
    letI : DecidableEq p.1 := p.2.2
    Matrix.trace (Equiv.Perm.permMatrix ℂ (Equiv.prodComm p.1 p.1)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
