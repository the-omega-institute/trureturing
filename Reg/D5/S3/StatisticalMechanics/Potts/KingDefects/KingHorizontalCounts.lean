import D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCaseReadouts

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference

noncomputable section

namespace interior_count

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c d : ℕ),
    N_e (.H (cut_row (a + 1) (b + 1)) (pivot c d) :
      Edge ((a + 1) + (b + 1) + 1) (c + (d + 1) + 1)) = R.readout () () ((E (a+b) c d + 2^(a+b) + P a b c d + P a b d c + Q a b c d + Q a b d c))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 1 1
  have ha := interior_count 1 1 1 1
  omega

def family : Registration arena (type_of% @interior_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_count.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_count

namespace horizontal_two_rows

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (M : ℕ),
    N_H 1 M = R.readout () () ((M * 2 ^ M))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1
  have ha := horizontal_two_rows 1
  omega

def family : Registration arena (type_of% @horizontal_two_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@horizontal_two_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@horizontal_two_rows) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_two_rows.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_two_rows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
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

end horizontal_two_rows

namespace boundary_one_column

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ),
    N_e (.H 0 (0 : Fin 1) : Edge (m + 1 + 1) 2) = R.readout () () (2 ^ m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1
  have ha := boundary_one_column 1
  omega

def family : Registration arena (type_of% @boundary_one_column) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_one_column, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_one_column) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.boundary_one_column.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.boundary_one_column.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
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

end boundary_one_column

namespace boundary_slots_one_column

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℕ),
    Nat.card {b : BoundaryData m 1 // BoundaryValid (0 : Fin 1) b} = R.readout () () (2 ^ m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1
  have ha := boundary_slots_one_column 1
  omega

def family : Registration arena (type_of% @boundary_slots_one_column) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_slots_one_column, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_slots_one_column) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.boundary_slots_one_column.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.boundary_slots_one_column.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
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

end boundary_slots_one_column

namespace interior_one_column_count

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 36 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (36 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : ℕ),
    N_e (.H (cut_row (a + 1) (b + 1)) (0 : Fin 1) :
      Edge ((a + 1) + (b + 1) + 1) 2) = R.readout () () (2 ^ (a + b))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1
  have ha := interior_one_column_count 1 1
  omega

def family : Registration arena (type_of% @interior_one_column_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_one_column_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (36 * (0 : ℕ)) ≠ (36 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_one_column_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_one_column_count.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_one_column_count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 36 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_one_column_count

namespace horizontal_two_columns

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ),
    N_H (p + 1) 1 = R.readout () () (((3 * p + 2) * 2 ^ p))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1
  have ha := horizontal_two_columns 1
  omega

def family : Registration arena (type_of% @horizontal_two_columns) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@horizontal_two_columns, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@horizontal_two_columns) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_two_columns.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_two_columns.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
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

end horizontal_two_columns

namespace interior_three_rows_count

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c d : ℕ),
    N_e (.H (1 : Fin 3) (pivot c d) : Edge 3 (c + (d + 1) + 1)) = R.readout () () ((2 ^ (c + d) + 2 ^ c + 2 ^ d + 3))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1
  have ha := interior_three_rows_count 1 1
  omega

def family : Registration arena (type_of% @interior_three_rows_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_three_rows_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_three_rows_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_three_rows_count.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_three_rows_count.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_three_rows_count

namespace horizontal_three_rows

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ),
    N_H 2 (q + 1) + 54 = R.readout () () (((q + 13) * 2 ^ q + 3 * (q + 2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1
  have ha := horizontal_three_rows 1
  omega

def family : Registration arena (type_of% @horizontal_three_rows) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@horizontal_three_rows, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@horizontal_three_rows) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_three_rows.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_three_rows.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
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

end horizontal_three_rows

namespace interior_row_sum

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b q : ℕ) (hm : 0 < a + b),
    (∑ s : Fin (q+2),
      N_e (.H (cut_row (a+1) (b+1)) s : Edge ((a+1)+(b+1)+1) (q+2+1))) + 48 = R.readout () () (((q+2)*2^(a+b+1) + 3*2^(q+2) + 2^(a+2) + 2^(b+2) +
        2*q*((if a=0 then 1 else 0)+(if b=0 then 1 else 0))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 1 (by norm_num)
  have ha := interior_row_sum 1 1 1 (by norm_num)
  omega

def family : Registration arena (type_of% @interior_row_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@interior_row_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@interior_row_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_row_sum.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.interior_row_sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end interior_row_sum

namespace boundary_row_sum

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m q : ℕ) (hm : 0 < m),
    (∑ s : Fin (q+2), N_e (.H (0 : Fin (m+2)) s : Edge (m+2) (q+2+1))) +
        12*(q+2)+12 = R.readout () () (((q+2)*2^m+2^(q+3)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 (by norm_num)
  have ha := boundary_row_sum 1 1 (by norm_num)
  omega

def family : Registration arena (type_of% @boundary_row_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@boundary_row_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@boundary_row_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.boundary_row_sum.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.boundary_row_sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end boundary_row_sum

namespace horizontal_sum

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t q : ℕ),
    N_H (t+3) (q+2) + 6*(8*(t+4)+4) = R.readout () () (((((t+4)*(q+2)+8)*2^(t+2))+(3*t+10)*2^(q+2)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1
  have ha := horizontal_sum 1 1
  omega

def family : Registration arena (type_of% @horizontal_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@horizontal_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@horizontal_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_sum.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.horizontal_sum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 6 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end horizontal_sum

namespace support_sizes_correct

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Σ _ : Fin 6, Fin 4) (fun p => Fin 4) (fun _ => ℕ × ℕ)

def actual : Realization signature :=
  realize signature (fun _ p x => support_sizes p.1 p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x => ((support_sizes p.1 p.2 x).1 + 1, (support_sizes p.1 p.2 x).2)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : NZPair) (i : Fin 6) (j k : Fin 4),
    (Nat.card (SupportAlphabet x (lower_pair x i) (supports j) (supports k)
      x.val.1 (lower_pair x i).val.1),
    Nat.card (SupportAlphabet x (lower_pair x i) (supports j) (supports k)
      x.val.2 (lower_pair x i).val.2)) = R.readout () ⟨i, j⟩ k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ⟨((1, 0), (0, 1)), by decide +kernel⟩ 0 0 0
  have ha := support_sizes_correct ⟨((1, 0), (0, 1)), by decide +kernel⟩ 0 0 0
  dsimp only [arena, rejected, realize] at hb
  have heq := congrArg Prod.fst (ha.symm.trans hb)
  exact (Nat.ne_of_lt (Nat.lt_succ_self _)) heq

def family : Registration arena (type_of% @support_sizes_correct) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@support_sizes_correct, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨⟨0, 0⟩, 0, 1, ?_⟩
    change support_sizes 0 0 0 ≠ support_sizes 0 0 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@support_sizes_correct) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.support_sizes_correct.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts.support_sizes_correct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => support_sizes p.1 p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
    definition := none
    coordinates := #[1, 2]
    readouts := #[{ path := #["body", "body", "body", "body", "arg"]
                    stateBinder := 0
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := some #["arg"] }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end support_sizes_correct



end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingHorizontalCounts
