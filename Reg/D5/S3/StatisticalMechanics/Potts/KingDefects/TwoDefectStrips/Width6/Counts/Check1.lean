import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
/-! Coordinate observations of the finite transfer identities. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxRecDepth 100000
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature (Fin 96)
  (fun _ => Fin 96) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ p s => T p s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ p s => T p s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : Fin 24, ∀ s : Fin 96,
    ((classList (⟨c.val, by omega⟩ : Fin 96)).count s : ℤ) =
      R.readout () (⟨c.val, by omega⟩ : Fin 96) s
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0 0
  have ha := counts 0 0
  change ((classList 0).count 0 : ℤ) = T 0 0 + 1 at hb
  change ((classList 0).count 0 : ℤ) = T 0 0 at ha
  linarith only [hb, ha]
def family : Registration arena (type_of% @counts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change T 0 0 ≠ T 0 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counts) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1.auditUnit
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
  readout := some (realize signature (fun _ p s => T p s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Counts.Check1
