import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Col column cls)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData (cross)
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 41) (fun _ => Fin 41) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ s r => S r s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ s r => S r s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (b : Col) (s : Fin 41),
    (∑ c : Col, if cross b (column c) = 2 ∧ cls c = s then (1 : ℤ) else 0) =
      A.readout () s (cls b)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0,0,0,0,0) 0
  have ha := quotient_rows (0,0,0,0,0) 0
  change _ = S (cls (0,0,0,0,0)) 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @quotient_rows) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨quotient_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change S 0 0 ≠ S 1 0
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@quotient_rows) (Realization signature) Type Unit where
  unitName := `Reg.A229698New.auditUnit
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
  readout := some (realize signature (fun _ s r => S r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripNew
