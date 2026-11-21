import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A dependent observation of the selected transfer operand. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 12) (fun _ => List State)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ j => weights ⟨12 + j.val, by omega⟩)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => 0 :: observation () p k) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Fin 12), let i : Fresh := ⟨12 + j.val, by omega⟩
    outgoing (rep i) (budget i) = R.readout () () j

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h 0
  have right := checked 0
  try dsimp only at wrong right
  change _ = 0 :: (weights ⟨12 + (0 : Fin 12).val, by omega⟩) at wrong
  rw [right] at wrong
  have lengths := congrArg List.length wrong
  simp at lengths

def family : Registration arena (type_of% @checked) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨checked, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change observation () () 0 ≠ observation () () 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checked) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Rows1.checked.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Rows1
