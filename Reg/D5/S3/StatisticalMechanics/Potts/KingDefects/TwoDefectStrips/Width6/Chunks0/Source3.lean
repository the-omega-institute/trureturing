import Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source2
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
import Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
/-! Successor observations at canonical source rows. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Sources
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
set_option maxRecDepth 100000
attribute [local irreducible] sources successors cl classList
noncomputable section
abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Fin 12) (fun _ => Row)
    (fun _ => List (Fin 96))
def actual : Realization signature :=
  realize signature (fun _ i p => successors p (sources ⟨0+i.val, by omega⟩).2.val) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ i p => successors p (sources ⟨0+i.val, by omega⟩).2.val ++ [0]) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ i : Fin 12, R.readout () i (sources ⟨0+i.val, by omega⟩).1 =
    classList (cl (sources ⟨0+i.val, by omega⟩).1 (sources ⟨0+i.val, by omega⟩).2.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := successor_rows 0
  change successors (sources ⟨0, by decide⟩).1 (sources ⟨0, by decide⟩).2.val ++ [0] = _ at hb
  have hh := congrArg List.length (hb.trans ha.symm)
  simp only [List.length_append, List.length_singleton, Fin.val_zero, Nat.add_zero] at hh
  omega
set_option maxHeartbeats 0 in
def family : Registration arena (type_of% @successor_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨successor_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, (fun _ => 0), ![0,1,0,1,0,1], ?_⟩
    exact _root_.Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Data.successors_vary _
set_option maxHeartbeats 0 in
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@successor_rows) (Realization signature) Type Unit where
  unitName := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3.auditUnit
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
  readout := some (realize signature (fun _ i p => successors p (sources ⟨0+i.val, by omega⟩).2.val) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "fn", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["fn", "arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.TwoDefectStrips.Width6.Chunks0.Source3
