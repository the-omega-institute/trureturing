import D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The original proper boundary class as the readout of the structural cut. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => Row) (fun _ => Fin 7)
def readout : Realization signature :=
  realize signature (fun _ _ r => HardinA233126SquareStrip.boundaryClass (true, true) r)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Fin 7)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p r : Row) (d : Fin 2) (s : Fin 12),
    ((d.val = 1 ∧ s.val < 6) ∨ (d.val = 0 ∧ 6 ≤ s.val)) →
    ((bondDefects (q := 3) between p r + bondDefects (q := 3) horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects (q := 3) between p r + bondDefects (q := 3) horizontal r r)) = s.castAdd 8) ↔
      HardinThinGraphTransport.proper r ∧ HardinThinGraphTransport.compatible true p r ∧
        R.readout () () r =
          ⟨s.val % 6 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 6); omega⟩)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 1, 0, 1, 0] ![0, 1, 0, 1, 0] 1 0 (by decide +kernel)
  have hc : bondDefects (q := 3) between (![0, 1, 0, 1, 0] : Row) ![0, 1, 0, 1, 0] +
      bondDefects (q := 3) horizontal ![0, 1, 0, 1, 0] ![0, 1, 0, 1, 0] ≤ 1 ∧
      cl ![0, 1, 0, 1, 0] (1 - (bondDefects (q := 3) between ![0, 1, 0, 1, 0] ![0, 1, 0, 1, 0] +
        bondDefects (q := 3) horizontal ![0, 1, 0, 1, 0] ![0, 1, 0, 1, 0])) = 0 := by decide +kernel
  have hf := (hb.mp hc).2.2
  change (0 : Fin 7) = 1 at hf
  exact (by decide : (0 : Fin 7) ≠ 1) hf
def family : Registration arena (type_of% @class_cut) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨class_cut, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ![0, 1, 0, 1, 2], ![0, 1, 0, 1, 0], ?_⟩
    change HardinA233126SquareStrip.boundaryClass (true, true) ![0, 1, 0, 1, 2] ≠
      HardinA233126SquareStrip.boundaryClass (true, true) ![0, 1, 0, 1, 0]
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_cut) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229531StripCut.auditUnit
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
  readout := some (realize signature
    (fun _ _ r => HardinA233126SquareStrip.boundaryClass (true, true) r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefects.HardinA229531StripCut
