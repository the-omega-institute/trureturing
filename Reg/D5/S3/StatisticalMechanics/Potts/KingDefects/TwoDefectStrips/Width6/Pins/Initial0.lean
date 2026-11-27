import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
/-! Coordinate observations of the finite transfer identities. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
set_option maxRecDepth 100000
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature (Unit)
  (fun _ => Fin 96) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ p s => initial s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ p s => initial s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ s : Fin 12,
      (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
        cl r (2-bondDefects horizontal r r) = (⟨0+s.val, by omega⟩ : Fin 96) then (1 : ℤ) else 0) = R.readout () () (⟨0+s.val, by omega⟩ : Fin 96)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 0
  have ha := certificate 0
  change _ = initial (⟨0, by decide⟩ : Fin 96) + 1 at hb
  simp only [Fin.val_zero, Nat.add_zero] at ha hb
  linarith only [hb,ha]
def family : Registration arena (type_of% @certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change initial 0 ≠ initial 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@certificate) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0.auditUnit
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
  readout := some (realize signature (fun _ p s => initial s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Initial0
