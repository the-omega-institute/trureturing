import LeanInformationAuditInterface.Contract.Registration
import D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
import Reg.Support.SingleDependentReadout

/-! Source-bound finite-word readouts on the full theorem telescopes. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.PrimeForms.Crossing.ExactPropagation
open _root_.D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced
open _root_.D5.S3.PrimeForms.SternBrocot.UnimodularGeneration

noncomputable section
namespace Reg.D5.S3.PrimeForms.SternBrocot.UnimodularGeneration

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => List Bool) (fun _ => PositiveMatrix)

def actual : Realization signature :=
  realize signature (fun _ _ u => wordMatrix u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => rootMatrix) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ A : PositiveMatrix, Unimodular A ↔ ∃ w : List Bool, R.readout () () w = A

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, hw⟩ := (h leftStep).mp unimodular_left
  have hc := congrArg PositiveMatrix.c hw
  norm_num [rejected, realize, rootMatrix, leftStep] at hc

def family : Registration arena (type_of% @unimodular_iff_wordMatrix) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unimodular_iff_wordMatrix, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), [], [false], ?_⟩
    intro h
    have hc := congrArg PositiveMatrix.c h
    norm_num [actual, realize, wordMatrix, rootMatrix, leftStep, PositiveMatrix.mul] at hc

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unimodular_iff_wordMatrix) (Realization signature) Unit Unit := {
  unitName := `D5.S3.PrimeForms.SternBrocot.UnimodularGeneration.unimodular_iff_wordMatrix.__information_unit
  realizationName := `Reg.D5.S3.PrimeForms.SternBrocot.UnimodularGeneration.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => wordMatrix u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
