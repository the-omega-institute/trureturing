import D5.S3.Combinatorics.TraceAvoidingArrays.FiveRow.HardinA233178Chromatic
import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Init.Core
import Init.Data.Bool
import Init.SimpLemmas

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip

open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip (cost cost_zero)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233178Chromatic (Column Bond)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Column (fun _ => Column) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ p q => decide (Bond p q)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p q : Column), cost p q = 0 ↔ R.readout () p q = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx : Bond (0 : Column) 121 := by decide +kernel
  exact Bool.false_ne_true ((h 0 121).mp ((cost_zero 0 121).mpr hx))

def family : Registration arena (type_of% @cost_zero) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using cost_zero,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 121, 0, ?_⟩
    change decide (Bond (0 : Column) 121) ≠ decide (Bond (0 : Column) 0)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@cost_zero) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229538Strip.auditUnit
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
  readout := some (realize signature (fun _ p q => decide (Bond p q)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a.HardinA229538Strip
