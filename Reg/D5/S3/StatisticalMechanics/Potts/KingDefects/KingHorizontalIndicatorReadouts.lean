import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference
open scoped IsAddKleinFour

noncomputable section

namespace sum_left_indicator

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ℕ (fun p => Fin (p + 2)) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p x => if x.val = 0 then 1 else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => (if x.val = 0 then 1 else 0) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ), (∑ i : Fin (t + 2), R.readout () t i) = (1 : ℕ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  dsimp only [arena, rejected, realize] at hb
  rw [Finset.sum_add_distrib, sum_left_indicator] at hb
  norm_num at hb

def family : Registration arena (type_of% @sum_left_indicator) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_left_indicator, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change (if (0 : Fin 2).val = 0 then (1 : ℕ) else 0) ≠ (if (1 : Fin 2).val = 0 then 1 else 0)
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_left_indicator) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.sum_left_indicator.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.sum_left_indicator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => if x.val = 0 then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "fn", "arg", "arg", "body"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end sum_left_indicator

namespace sum_right_indicator

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ℕ (fun p => Fin (p + 2)) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p x => if p + 1 - x.val = 0 then 1 else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => (if p + 1 - x.val = 0 then 1 else 0) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ), (∑ i : Fin (t + 2), R.readout () t i) = (1 : ℕ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  dsimp only [arena, rejected, realize] at hb
  rw [Finset.sum_add_distrib, sum_right_indicator] at hb
  norm_num at hb

def family : Registration arena (type_of% @sum_right_indicator) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_right_indicator, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change (if 0 + 1 - (0 : Fin 2).val = 0 then (1 : ℕ) else 0) ≠ (if 0 + 1 - (1 : Fin 2).val = 0 then 1 else 0)
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@sum_right_indicator) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.sum_right_indicator.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.sum_right_indicator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => if p + 1 - x.val = 0 then 1 else 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "fn", "arg", "arg", "body"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end sum_right_indicator

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
