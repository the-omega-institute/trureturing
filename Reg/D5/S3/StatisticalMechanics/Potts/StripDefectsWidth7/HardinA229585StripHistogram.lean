import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Input) (fun _ => ℤ)
def readout : Realization signature :=
  realize signature (fun _ _ x => histogram x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => histogram x + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : Input,
    (∑ r : Row, if cross x.1 r + bondDefects horizontal r r ≤ x.2.1.val ∧
      cl (boundary r) (x.2.1.val - (cross x.1 r + bondDefects horizontal r r)) = x.2.2
      then (1 : ℤ) else 0) = R.readout () () x
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let x : Input := (![0, 1, 0, 1, 0, 1], 1, 0)
  have hb := h x
  have ha := sum_filtered x
  change _ = histogram x + 1 at hb
  linarith
def family : Registration arena (type_of% @sum_filtered) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨sum_filtered, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (![0, 1, 0, 1, 0, 1], 1, 0), (![0, 1, 0, 1, 0, 1], 0, 0), ?_⟩
    change histogram _ ≠ histogram _
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_filtered) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram.auditUnit
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
  readout := some (realize signature (fun _ _ x => histogram x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripHistogram
