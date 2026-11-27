import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Fin 11) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ p j => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.transfer (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.boundaryClass (true, true) p) j) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ p j => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.transfer (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.boundaryClass (true, true) p) j + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (p : Row), _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper p → ∀ j : Fin 11,
    64 * (∑ r : Row, if _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper r ∧
      (∀ i : Fin 6, p i ≠ r i) ∧
      _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.boundaryClass (true, true) r = j
      then (1 : ℤ) else 0) = ρ.readout () p j
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) 1
  have ha := raw_successors (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) 1
  change _ = _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.transfer
    (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.boundaryClass (true, true) ![0, 1, 0, 1, 0, 1]) 1 + 1 at hb
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @raw_successors) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨raw_successors, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 1, 0, 1, 0, 1], 0, 1, ?_⟩
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@raw_successors) (Realization signature) Type Unit where
  unitName := `Reg.ProperTransfer.auditUnit
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
  readout := some (realize signature (fun _ p j => _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.transfer (_root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127SquareStrip.boundaryClass (true, true) p) j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
