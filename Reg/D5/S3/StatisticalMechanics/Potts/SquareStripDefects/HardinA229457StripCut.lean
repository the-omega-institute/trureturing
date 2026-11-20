import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233127Rows
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! The original proper boundary class as the readout of the structural cut. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Cut
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => Row) (fun _ => Fin 11)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature :=
  realize signature (fun _ _ r => HardinA233127SquareStrip.boundaryClass (true, true) r)
    (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : Fin 11)) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (p r : Row) (d : Fin 2) (s : Fin 20),
    ((d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) →
    ((bondDefects (q := 3) ProperTransfer.between p r + bondDefects (q := 3) horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects (q := 3) ProperTransfer.between p r + bondDefects (q := 3) horizontal r r)) = s.castAdd 22) ↔
      HardinThinGraphTransport.proper r ∧ (∀ i : Fin 6, p i ≠ r i) ∧
        ρ.readout () () r =
          ⟨s.val % 10 + 1, by have := Nat.mod_lt s.val (by omega : 0 < 10); omega⟩)
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![1, 0, 1, 0, 1, 0] ![0, 1, 0, 1, 0, 1] 1 0 (by decide +kernel)
  have hc : bondDefects (q := 3) ProperTransfer.between (![1, 0, 1, 0, 1, 0] : Row) ![0, 1, 0, 1, 0, 1] +
      bondDefects (q := 3) horizontal ![0, 1, 0, 1, 0, 1] ![0, 1, 0, 1, 0, 1] ≤ 1 ∧
      cl ![0, 1, 0, 1, 0, 1] (1 - (bondDefects (q := 3) ProperTransfer.between ![1, 0, 1, 0, 1, 0] ![0, 1, 0, 1, 0, 1] +
        bondDefects (q := 3) horizontal ![0, 1, 0, 1, 0, 1] ![0, 1, 0, 1, 0, 1])) = 0 := by decide +kernel
  have hf := (hb.mp hc).2.2
  change (0 : Fin 11) = 1 at hf
  exact (by decide : (0 : Fin 11) ≠ 1) hf
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @class_cut) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨class_cut, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ![0, 1, 0, 1, 0, 2], ![0, 1, 0, 1, 0, 1], ?_⟩
    change HardinA233127SquareStrip.boundaryClass (true, true) ![0, 1, 0, 1, 0, 2] ≠
      HardinA233127SquareStrip.boundaryClass (true, true) ![0, 1, 0, 1, 0, 1]
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_cut) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229457StripCut.auditUnit
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
    (fun _ _ r => HardinA233127SquareStrip.boundaryClass (true, true) r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
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
end Cut
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace ProperCounts
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Row, Fin 2) (fun _ => Fin 20) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ pd s => T (cl pd.1 pd.2.val) (s.castAdd 22)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ pd s => T (cl pd.1 pd.2.val) (s.castAdd 22) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (p : Row) (d : Fin 2), _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinThinGraphTransport.proper p →
    ∀ s : Fin 20, ((d.val = 1 ∧ s.val < 10) ∨ (d.val = 0 ∧ 10 ≤ s.val)) →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = s.castAdd 22
      then (1 : ℤ) else 0) = ρ.readout () ⟨p, d⟩ s
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel) 0 (by decide +kernel)
  have ha := proper_counts (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel) 0 (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 at ha
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @proper_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨proper_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨![0, 1, 0, 1, 0, 1], 1⟩, 0, 1, ?_⟩
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@proper_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229457StripCutProperCounts.auditUnit
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
  readout := some (realize signature (fun _ pd s => T (cl pd.1 pd.2.val) (s.castAdd 22)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ProperCounts
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace ActiveCounts
/- signature: proof_shape=bind-only; consumers=readout, rejected, arena, audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Fin 10, Row) (fun _ => Fin 2) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=family -/
def readout : Realization signature := realize signature (fun _ jp d => T (cl jp.2 d.val) (jp.1.castAdd 32)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law, family -/
def rejected : Realization signature := realize signature (fun _ jp d => T (cl jp.2 d.val) (jp.1.castAdd 32) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law, family, audit -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (j : Fin 10) (p : Row) (d : Fin 2), Valid p d.val →
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.castAdd 32
      then (1 : ℤ) else 0) = ρ.readout () ⟨j, p⟩ d
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel)
  have ha := active_counts 0 (![0, 1, 0, 1, 0, 1] : Row) 1 (by decide +kernel)
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 0 at ha
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @active_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨active_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0, ![0, 1, 0, 1, 0, 1]⟩, 0, 1, ?_⟩
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=compiled Contract.Registration inspection -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@active_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229457StripCutActiveCounts.auditUnit
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
  readout := some (realize signature (fun _ jp d => T (cl jp.2 d.val) (jp.1.castAdd 32)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ActiveCounts
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripCut
