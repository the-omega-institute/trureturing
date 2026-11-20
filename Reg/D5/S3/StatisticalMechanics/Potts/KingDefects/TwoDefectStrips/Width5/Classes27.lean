import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes27
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The successor list is the varying observed value. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes27
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes27
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxRecDepth 100000
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Fin 3) (fun _ => Row)
    (fun _ => List (Fin 43))
def actual : Realization signature :=
  realize signature (fun _ d p => successors p d.val) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ d p => successors p d.val ++ [0]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p (d : Fin 3), Valid p d.val → Canonical p → cl p d.val = 27 →
    R.readout () d p = classList 27
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Row := ![0, 1, 1, 2, 3]
  have hp : Valid p 1 := by decide +kernel
  have hc : Canonical p := by unfold Canonical; decide +kernel
  have hi : cl p 1 = 27 := by decide +kernel
  have hb := h p ⟨1, by decide⟩ hp hc hi
  have ha := class_successors p ⟨1, by decide⟩ hp hc hi
  change successors p 1 ++ [0] = classList 27 at hb
  have hh := congrArg List.length (hb.trans ha.symm)
  simp only [List.length_append, List.length_singleton] at hh
  omega
def family : Registration arena (type_of% @class_successors) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨class_successors, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨0, by decide⟩, (fun _ => 0), ![0,1,0,1,0], ?_⟩
    exact _root_.Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Data.successors_vary
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_successors) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes27.auditUnit
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
  readout := some (realize signature (fun _ d p => successors p d.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes27
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["fn", "arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width5.Classes27
