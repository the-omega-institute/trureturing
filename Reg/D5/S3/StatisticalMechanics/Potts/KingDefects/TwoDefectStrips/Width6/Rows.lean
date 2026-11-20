import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
/-! Canonical reconstruction as a row-valued observation. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Row (fun _ => Fin 187) (fun _ => Row)
def actual : Realization signature :=
  realize signature (fun _ _ i => rows i) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ i j => rows i j + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Row, Canonical p → R.readout () p (rowIndex p) = p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : Canonical (fun _ : Fin 6 => (0 : Fin 4)) := by unfold Canonical; decide +kernel
  have hb := congrFun (h (fun _ => 0) hc) 0
  have ha := congrFun (reconstruction (fun _ => 0) hc) 0
  change rows (rowIndex (fun _ => 0)) 0 + 1 = 0 at hb
  rw [ha] at hb
  norm_num at hb
def family : Registration arena (type_of% @reconstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reconstruction, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => 0), 0, 1, ?_⟩
    change rows 0 ≠ rows 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@reconstruction) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows.auditUnit
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
  readout := some (realize signature (fun _ _ i => rows i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Rows
