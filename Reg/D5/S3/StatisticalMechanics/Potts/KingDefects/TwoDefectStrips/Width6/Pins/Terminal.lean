import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
/-! Coordinate observations of the finite transfer identities. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxRecDepth 100000
noncomputable section
abbrev signature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature (Fin 3)
  (fun _ => Fin 96) (fun _ => ℤ)
def actual : Realization signature := realize signature (fun _ p s => terminal s) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ p s => terminal s + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p (d : Fin 3), Valid p d.val → R.readout () d (cl p d.val) = (if d.val=0 then 1 else 0)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  let p : Row := ![0,0,1,0,1,0]
  have hp : Valid p 0 := by decide +kernel
  have hb := h p 0 hp
  have ha := certificate p 0 hp
  change terminal (cl p 0) + 1 = 1 at hb
  change terminal (cl p 0) = 1 at ha
  linarith only [hb,ha]
def family : Registration arena (type_of% @certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 73, ?_⟩
    change terminal 0 ≠ terminal 73
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@certificate) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal.auditUnit
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
  readout := some (realize signature (fun _ p s => terminal s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Pins.Terminal
