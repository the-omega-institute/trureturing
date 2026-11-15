import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option profiler true

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 72) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ r => initial r) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ r => initial r + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Fin 72, 32 ≤ s.val ∧ s.val < 40 →
    (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = R.readout () () s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 32 (by decide)
  have ha := initial_counts 32 (by decide)
  change _ = initial 32 + 1 at hb
  linarith
def family : Registration arena (type_of% @initial_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨initial_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 32, 33, ?_⟩
    change initial 32 ≠ initial 33
    unfold initial
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_counts) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4.auditUnit
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
  readout := some (realize signature (fun _ _ r => initial r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.Initial.HardinA229585StripCounts4
