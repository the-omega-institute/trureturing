import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass1
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass1
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass1
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Fin 4, Row) (fun _ => Fin 2) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ jp d => T (cl jp.2 d.val) ⟨14 + jp.1.val, by omega⟩) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ jp d => T (cl jp.2 d.val) ⟨14 + jp.1.val, by omega⟩ + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (j : Fin 4) p (d : Fin 2), Valid p d.val → Canonical p →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (⟨14 + j.val, by omega⟩ : Fin 42)
      then (1 : ℤ) else 0) = ρ.readout () ⟨j, p⟩ d
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel) (by unfold Canonical; decide +kernel)
  have ha := transition_counts 0 (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel) (by unfold Canonical; decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 14 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 14 at ha
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
    refine ⟨⟨0, ![0, 1, 0, 1, 0, 1]⟩, 0, 1, ?_⟩
    change T (cl ![0, 1, 0, 1, 0, 1] 0) 14 ≠ T (cl ![0, 1, 0, 1, 0, 1] 1) 14
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229457StripClass1.auditUnit
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
  readout := some (realize signature (fun _ jp d => T (cl jp.2 d.val) ⟨14 + jp.1.val, by omega⟩) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass1
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripClass1
