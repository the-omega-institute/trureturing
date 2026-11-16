import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22
import Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The successor list is the varying observed value. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxRecDepth 100000
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Fin 3 × Fin 3) (fun _ => Row)
    (fun _ => List (Fin 96))
def actual : Realization signature :=
  realize signature (fun _ d p => successors p d.2.val) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ d p => successors p d.2.val ++ [0]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : Fin 3) p (d : Fin 3), Valid p d.val → Canonical p → cl p d.val = (⟨66+c.val, by omega⟩ : Fin 96) →
    R.readout () (c,d) p = classList ⟨66+c.val, by omega⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let p : Row := ![0,1,0,2,1,3]
  have hp : Valid p 1 := by decide +kernel
  have hc : Canonical p := by unfold Canonical; decide +kernel
  have hi : cl p 1 = (⟨66, by decide⟩ : Fin 96) := by decide +kernel
  have hb := h 0 p ⟨1, by decide⟩ hp hc hi
  have ha := class_successors 0 p ⟨1, by decide⟩ hp hc hi
  change successors p 1 ++ [0] = classList ⟨66, by decide⟩ at hb
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
    refine ⟨(0,0), (fun _ => 0), ![0,0,0,0,0,0], ?_⟩
    exact _root_.Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data.successors_vary
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@class_successors) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22.auditUnit
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
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22
    definition := none
    coordinates := #[0, 2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["fn", "arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Classes22
