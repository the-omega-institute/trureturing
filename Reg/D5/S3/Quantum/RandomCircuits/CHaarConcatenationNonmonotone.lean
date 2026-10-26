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

/-- Observe the complex cardinality appearing in the swap trace identity. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => (k : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The trace identity keeps the complete polymorphic telescope. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : Type u} [Fintype n] [DecidableEq n],
    Matrix.trace (Equiv.Perm.permMatrix ℂ (Equiv.prodComm n n)) =
      r.readout () () (Fintype.card n)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hbad := @h (ULift.{u} (Fin 1)) inferInstance inferInstance
  change Matrix.trace (Equiv.Perm.permMatrix ℂ
    (Equiv.prodComm (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)))) = 0 at hbad
  rw [traceSwap] at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

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
      (Realization signature) Unit Unit := {
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
  readout := some (realize signature (fun _ _ k => (k : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.RandomCircuits.CHaarConcatenationNonmonotone
