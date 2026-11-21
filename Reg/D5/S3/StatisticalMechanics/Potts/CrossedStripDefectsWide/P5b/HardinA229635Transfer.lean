import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observations of the checked transition, initial and terminal weights. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row)
open scoped BigOperators

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace TerminalCorrect

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ d => if d = 0 then 1 else 0)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => observation () p k + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Row) (d : ℕ), Valid p d → terminal (cl p d) = R.readout () () d

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (![0, 1, 0, 1, 0, 1] : Row) 0 (by decide +kernel)
  have right := terminal_correct (![0, 1, 0, 1, 0, 1] : Row) 0 (by decide +kernel)
  dsimp only [altered, realize, observation] at wrong
  omega

def family : Registration arena (type_of% @terminal_correct) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨terminal_correct, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change observation () () 0 ≠ observation () () 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@terminal_correct) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635Transfer.terminal_correct.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TerminalCorrect


end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Transfer
