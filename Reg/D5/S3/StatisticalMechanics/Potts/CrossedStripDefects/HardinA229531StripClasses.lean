import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Faithful readout of the exact HDA successor count. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Row, Fin 2) (fun _ => Fin 20) (fun _ => ℤ)
def readout : Realization signature :=
  realize signature (fun _ pd s => T (cl pd.1 pd.2.val) s) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ pd s => T (cl pd.1 pd.2.val) s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 20,
    (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = R.readout () ⟨p, d⟩ s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0] : Row) 1 (by decide +kernel) 0
  have ha := transition_counts (![0, 1, 0, 1, 0] : Row) 1 (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0] 1) 0 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0] 1) 0 at ha
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨![0, 1, 0, 1, 0], 1⟩, 0, 1, ?_⟩
    change T (cl ![0, 1, 0, 1, 0] 1) 0 ≠ T (cl ![0, 1, 0, 1, 0] 1) 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229531StripClasses.auditUnit
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
  readout := some (realize signature (fun _ pd s => T (cl pd.1 pd.2.val) s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripClasses
