import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks02.Block0207
import Reg.Support.BooleanCheckerReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The selected source readout checks the complete literal row list. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.SmallPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks02.Block0207

attribute [local irreducible] checkBlock checkRows checkPrime

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => List Row) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ xs => checkBlock 1695747 4096 xs) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () rows0207 = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change false = true at h
  cases h
private theorem empty_rejected : checkBlock 1695747 4096 [] = false := by
  decide +kernel

def family : Registration arena (type_of% @checked0207) where
  actual := actual
  bridge := Reg.Support.BooleanCheckerReadout.bridge
    (checkBlock 1695747 4096) rows0207
  variation := ⟨checked0207, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := Reg.Support.BooleanCheckerReadout.dependence
    (checkBlock 1695747 4096) rows0207 [] checked0207 empty_rejected

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    checked0207 (Realization signature) (List Row) Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checked0207.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks02.Block0207.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ xs => checkBlock 1695747 4096 xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some rows0207
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks02.Block0207
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks02.Block0207
