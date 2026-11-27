import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A dependent observation of the selected transfer operand. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Powers
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseData

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 10) (fun _ => State → ℤ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ k => power (⟨10 + k.val, by omega⟩ : Fin 30).succ)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k s => observation () p k s + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : Fin 10), let i : Fin 30 := ⟨10 + k.val, by omega⟩
    R.readout () () k = step (power i.castSucc)

private theorem rejected : ¬ arena.Law altered := by
  intro h
  let i : Fin 30 := ⟨10, by decide⟩
  have wrong := congrFun (h 0) 31
  have right := congrFun (checked 0) 31
  change power i.succ 31 + 1 = step (power i.castSucc) 31 at wrong
  change power i.succ 31 = step (power i.castSucc) 31 at right
  have addOne (a : ℤ) : a + 1 ≠ a := by omega
  exact addOne _ (wrong.trans right.symm)

def family : Registration arena (type_of% @checked) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨checked, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change observation () () 0 ≠ observation () () 1
    intro eq
    have same := congrFun eq 31
    apply (show observation () () 0 31 ≠ observation () () 1 31 by decide +kernel)
    exact same

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checked) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635PowerCheck1.checked.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635PowerCheck1
