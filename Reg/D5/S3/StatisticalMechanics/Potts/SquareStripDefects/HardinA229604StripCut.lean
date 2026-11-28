import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData

import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
import D5.S3.StatisticalMechanics.Potts.SquareStripDefects.ProperTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option maxRecDepth 100000

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace LeadingCounts
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row × Fin 3) (fun _ => Fin 42) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ pd j => T (cl pd.1 pd.2.val) (j.castAdd 54)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ pd j => T (cl pd.1 pd.2.val) (j.castAdd 54) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (p : Row) (d : Fin 3), Valid p d.val → ∀ j : Fin 42,
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ d.val ∧
      cl r (d.val - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = j.castAdd 54
      then (1 : ℤ) else 0) = ρ.readout () (p, d) j
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) 2 (by decide +kernel) 0
  have ha := leading_counts (![0, 1, 0, 1, 0, 1] : Row) 2 (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 2) 0 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 2) 0 at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @leading_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨leading_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(![0, 1, 0, 1, 0, 1], 2), 0, 1, ?_⟩
    change T (cl ![0, 1, 0, 1, 0, 1] 2) 0 ≠ T (cl ![0, 1, 0, 1, 0, 1] 2) 1
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@leading_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripCutLeadingCounts.auditUnit
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
  readout := some (realize signature (fun _ pd j => T (cl pd.1 pd.2.val) (j.castAdd 54)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
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
end LeadingCounts
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace TerminalCounts
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Fin 32) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ p j => T (cl p 0) ((j.natAdd 42).castAdd 22)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ p j => T (cl p 0) ((j.natAdd 42).castAdd 22) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ p : Row, bondDefects horizontal p p ≤ 1 → ∀ j : Fin 32,
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ 0 ∧
      cl r (0 - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (j.natAdd 42).castAdd 22
      then (1 : ℤ) else 0) = ρ.readout () p j
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) 0
  have ha := terminal_counts (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 0) 42 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 0) 42 at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @terminal_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨terminal_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 1, 0, 1, 0, 1], 0, 1, ?_⟩
    change T (cl ![0, 1, 0, 1, 0, 1] 0) 42 ≠ T (cl ![0, 1, 0, 1, 0, 1] 0) 43
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@terminal_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripCutTerminalCounts.auditUnit
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
  readout := some (realize signature (fun _ p j => T (cl p 0) ((j.natAdd 42).castAdd 22)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
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
end TerminalCounts
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace OneDefectCounts
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Fin 32) (fun _ => ℤ)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ p j => T (cl p 1) ((j.natAdd 42).castAdd 22)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ p j => T (cl p 1) ((j.natAdd 42).castAdd 22) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ p : Row, bondDefects horizontal p p = 0 → ∀ j : Fin 32,
    (∑ r : Row, if bondDefects ProperTransfer.between p r + bondDefects horizontal r r ≤ 1 ∧
      cl r (1 - (bondDefects ProperTransfer.between p r + bondDefects horizontal r r)) = (j.natAdd 42).castAdd 22
      then (1 : ℤ) else 0) = ρ.readout () p j
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) 0
  have ha := one_defect_counts (![0, 1, 0, 1, 0, 1] : Row) (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 42 + 1 at hb
  change _ = T (cl ![0, 1, 0, 1, 0, 1] 1) 42 at ha
  linarith
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @one_defect_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨one_defect_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 1, 0, 1, 0, 1], 0, 1, ?_⟩
    change T (cl ![0, 1, 0, 1, 0, 1] 1) 42 ≠ T (cl ![0, 1, 0, 1, 0, 1] 1) 43
    decide +kernel
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@one_defect_counts) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripCutOneDefectCounts.auditUnit
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
  readout := some (realize signature (fun _ p j => T (cl p 1) ((j.natAdd 42).castAdd 22)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
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
end OneDefectCounts
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut

/-! Exact original readouts for the six-column square strip. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripData
open _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row horizontal)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
namespace ActiveCut
/- signature: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × Fin 3) (fun _ => Row) (fun _ => Fin 42)
/- readout: proof_shape=bind-only; consumers=typed registration evidence -/
def readout : Realization signature := realize signature (fun _ cd r => _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData.cl r (cd.2.val - 1 - cd.1)) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=typed registration evidence -/
def rejected : Realization signature := realize signature (fun _ cd r => _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData.cl r (cd.2.val - 1 - cd.1) + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=typed registration evidence -/
abbrev arena : Arena where
  signature := signature
  Law ρ := ∀ (r : Row) (c : ℕ) (d : Fin 3) (j : Fin 42), 0 < d.val →
    ((c ≤ d.val ∧ cl r (d.val - c) = j.castAdd 54) ↔
      c ≤ d.val - 1 ∧ ρ.readout () (c, d) r = j)
/- rejected_law: proof_shape=bind-only; consumers=typed registration evidence -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (![0, 1, 0, 1, 0, 1] : Row) 0 1 10 (by decide +kernel)
  have hc : 0 ≤ (1 : Fin 3).val ∧ cl (![0, 1, 0, 1, 0, 1] : Row) (1 - 0) = (10 : Fin 42).castAdd 54 := by decide +kernel
  have hf := (hb.mp hc).2
  change (11 : Fin 42) = 10 at hf
  exact (by decide : (11 : Fin 42) ≠ 10) hf
/- family: proof_shape=bind-only; consumers=typed registration evidence -/
def family : Registration arena (type_of% @active_cut) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨active_cut, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0, 1), ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 2], ?_⟩
    decide +kernel +revert
/- audit: proof_shape=bind-only; consumers=typed registration evidence -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@active_cut) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229604StripCutActiveCut.auditUnit
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
  readout := some (realize signature (fun _ cd r => _root_.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229457StripData.cl r (cd.2.val - 1 - cd.1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ActiveCut
end
end Reg.D5.S3.StatisticalMechanics.Potts.SquareStripDefects.HardinA229604StripCut
