import D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
import Reg.Support.UniverseSingleReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-equivalent readout laws for king-graph defect counts. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference

open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects
open _root_.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open KingGrid KingDifference

noncomputable section

namespace add_eq_zero

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature K (fun _ => K) (fun _ => K)

def actual : Realization signature :=
  realize signature (fun _ a b => a + b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ a b => a + b + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b : K), R.readout () a b = 0 ↔ a = b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 0 0).mpr rfl
  simpa [rejected, realize] using hb

def family : Registration arena (type_of% @KingDifference.add_eq_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@KingDifference.add_eq_zero, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨0, 0, 1, ?_⟩
    change (0 + 0 : K) ≠ 0 + 1
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@KingDifference.add_eq_zero) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.add_eq_zero.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.add_eq_zero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a b => a + b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg", "fn", "arg"]
                    stateBinder := 1
                    functionOperand := false
                    booleanPredicate := false
                    stateOperand := none }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end add_eq_zero

namespace count_by_kind

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 6 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (6 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M),
    N_H N M + N_H M N + 2 * N_D N M = R.readout () () (T (N + 1) (M + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := h 1 1 (by norm_num) (by norm_num)
  have ha := count_by_kind 1 1 (by norm_num) (by norm_num)
  omega

def family : Registration arena (type_of% @count_by_kind) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_by_kind, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (6 * (0 : ℕ)) ≠ (6 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_by_kind) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.count_by_kind.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.count_by_kind.family
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
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
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

end count_by_kind

namespace count_fixed_edge

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ x => 4 * x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ x => (4 * x) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N M : ℕ} (e : Edge (N + 1) (M + 1)),
    Nat.card {f : Cell (N + 1) (M + 1) → Fin 4 // DefectAt e f} = R.readout () () (N_e e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp only [arena, rejected, realize] at h
  have hb := @h 1 1 (.H 0 0)
  have ha := @count_fixed_edge 1 1 (.H 0 0)
  omega

def family : Registration arena (type_of% @count_fixed_edge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@count_fixed_edge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, 1, ?_⟩
    change (4 * (0 : ℕ)) ≠ (4 * (1 : ℕ))
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_fixed_edge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.count_fixed_edge.auditUnit
  realizationName := `Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference.count_fixed_edge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => 4 * x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
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

end count_fixed_edge

end
end Reg.D5.S3.StatisticalMechanics.Potts.KingDefects.KingDifference
