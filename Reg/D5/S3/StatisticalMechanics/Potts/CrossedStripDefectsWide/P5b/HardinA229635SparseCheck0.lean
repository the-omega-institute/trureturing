import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck0
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! A dependent observation of the selected transfer operand. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck0

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck0
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseData

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 32) (fun _ => List State)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ j => incomingClasses ⟨0 + j.val, by omega⟩)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => 0 :: observation () p k) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (j : Fin 32), let k : State := ⟨0 + j.val, by omega⟩
    R.readout () () j = transposeLists k

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h 0
  have right := exact_transpose 0
  try dsimp only at wrong right
  change 0 :: (incomingClasses ⟨0 + (0 : Fin 32).val, by omega⟩) = _ at wrong
  rw [← right] at wrong
  have lengths := congrArg List.length wrong
  simp at lengths

def family : Registration arena (type_of% @exact_transpose) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exact_transpose, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change observation () () 0 ≠ observation () () 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@exact_transpose) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635SparseCheck0.exact_transpose.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck0
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

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635SparseCheck0
