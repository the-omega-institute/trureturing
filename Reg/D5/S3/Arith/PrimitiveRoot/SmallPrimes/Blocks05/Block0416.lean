import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416
import Reg.Support.BooleanCheckerReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The selected source readout checks the complete literal row list. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.SmallPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416

attribute [local irreducible] checkBlock checkRows checkPrime

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => List Row) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ _ xs => checkBlock 3407875 4096 xs) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () rows0416 = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change false = true at h
  cases h
private theorem empty_rejected : checkBlock 3407875 4096 [] = false := by
  decide +kernel

def family : Registration arena (type_of% @checked0416) where
  actual := actual
  bridge := Reg.Support.BooleanCheckerReadout.bridge
    (checkBlock 3407875 4096) rows0416
  variation := ⟨checked0416, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := Reg.Support.BooleanCheckerReadout.dependence
    (checkBlock 3407875 4096) rows0416 [] checked0416 empty_rejected

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    checked0416 (Realization signature) (List Row) Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checked0416.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416.family
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
    (fun _ _ xs => checkBlock 3407875 4096 xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some rows0416
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416
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
end Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Blocks05.Block0416
