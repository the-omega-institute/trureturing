import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, Fin 15) (fun _ => Row 3 6) (fun _ => ℤ)
def readout : Realization signature := realize signature
  (fun _ x q => ∑ r : Row 3 6, if bondDefects (betw 6) q r = x.1 ∧
    boundary r = x.2 then (1 : ℤ) else 0) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ x q => readout.readout () x q + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law a := ∀ (d : ℕ) (p q : Row 3 6) (j : Fin 15), boundary p = boundary q →
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = d ∧ boundary r = j
      then (1 : ℤ) else 0) = a.readout () ⟨d, j⟩ q
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 (representatives 0) (representatives 0) 0 rfl
  change _ = (∑ r : Row 3 6, if bondDefects (betw 6)
    (representatives 0) r = 0 ∧ boundary r = 0 then (1 : ℤ) else 0) + 1 at hb
  linarith

def family : Registration arena (type_of% @lift_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨lift_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0, 0⟩, representatives 0, representatives 1, ?_⟩
    have rep : ∀ i : Fin 15, boundary (representatives i) = i := by decide +kernel
    change (∑ r : Row 3 6, if bondDefects (betw 6) (representatives 0) r = 0 ∧
        boundary r = 0 then (1 : ℤ) else 0) ≠
      ∑ r : Row 3 6, if bondDefects (betw 6) (representatives 1) r = 0 ∧
        boundary r = 0 then (1 : ℤ) else 0
    rw [counts (representatives 0) 0, counts (representatives 1) 0, rep, rep]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@lift_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203981StripSymmetry.auditUnit
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
  readout := some readout
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
    definition := none
    coordinates := #[0, 3]
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
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripSymmetry
