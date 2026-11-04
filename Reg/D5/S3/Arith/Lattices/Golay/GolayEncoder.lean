import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Lattices.Golay.GolayEncoder
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Lattices.Golay.GolayEncoder
open _root_.D5.S3.Arith.Lattices.Golay.GolayEncoder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Message) (fun _ => Word)

def actual : Realization signature :=
  realize signature (fun _ _ m => encode m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Function.Injective (R.readout () ())

private theorem message_distinct : message 0 ≠ message 1 := by decide +kernel

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact message_distinct (h (by rfl))

def evidence : Registration arena (Function.Injective encode) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨encode_injective, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := by
    intro i
    refine ⟨(), message 0, message 1, ?_⟩
    exact fun h => message_distinct (encode_injective h)

def injectivityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.Lattices.Golay.GolayEncoder.encode_injective)
    (type_of% (realize signature (fun _ _ m => encode m) (fun e => nomatch e)))
    Unit Unit where
  unitName := `Reg.D5.S3.Arith.Lattices.Golay.GolayEncoder.injectivityUnit
  realizationName := `Reg.D5.S3.Arith.Lattices.Golay.GolayEncoder.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ m => encode m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.Golay.GolayEncoder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.Lattices.Golay.GolayEncoder
