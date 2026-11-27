import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3) (fun _ => Row) (fun _ => Fin 96)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ d p => cl p d.val) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : Fin 96)) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (j : Fin 22) (p : Row) (d : Fin 3), d.val < 2 →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.natAdd 74
      then (1 : ℤ) else 0) = T (ρ.readout () d p) (j.natAdd 74)
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (![0, 1, 0, 1, 0, 1] : Row) 0 (by decide)
  have ha := transition_counts 0 (![0, 1, 0, 1, 0, 1] : Row) 0 (by decide)
  change _ = T 0 74 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 0) 74 at ha
  have ht : T 0 74 ≠ T (cl ![0, 1, 0, 1, 0, 1] 0) 74 := by decide +kernel
  exact ht (hb.symm.trans ha)
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 2], ?_⟩
    change cl ![0, 1, 0, 1, 0, 1] 0 ≠ cl ![0, 1, 0, 1, 0, 2] 0
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripLastCut.auditUnit
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
  readout := some (realize signature (fun _ d p => cl p d.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripLastCut
