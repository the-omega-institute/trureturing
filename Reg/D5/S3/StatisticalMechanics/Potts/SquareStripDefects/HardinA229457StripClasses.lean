import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Faithful readout of the exact square-lattice successor count. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Row, Fin 2) (fun _ => Fin 42) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature :=
  realize signature (fun _ pd s => T (cl pd.1 pd.2.val) s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature :=
  realize signature (fun _ pd s => T (cl pd.1 pd.2.val) s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 42,
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s
      then (1 : ℤ) else 0) = ρ.readout () ⟨p, d⟩ s
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel) 0
  have ha := transition_counts (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 at ha
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 at ha
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨![0, 1, 0, 1, 0, 1], 1⟩, 0, 1, ?_⟩
    change T (cl ![0, 1, 0, 1, 0, 1] 1) 0 ≠ T (cl ![0, 1, 0, 1, 0, 1] 1) 1
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229457StripClasses.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
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
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClasses
