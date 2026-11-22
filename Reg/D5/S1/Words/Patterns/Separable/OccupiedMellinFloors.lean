import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinFloors
import Reg.Support.DependentFamily

/-! The uniform mesh error allowance changes with the mesh size. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinFloors

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinFloors
open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => 1232 * r ^ (-(1 / 80 : ℝ))) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {β : ℝ}, 0 ≤ β → β ≤ 3 / 4 → ∀ n : ℕ, 4 ^ 20 ≤ n →
    Summable (fun i : ℕ => |sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)|) ∧
    IntegrableOn (sample β 0) (Set.Ioi 0) ∧
    |(∫ t in Set.Ioi (0 : ℝ), sample β 0 t) -
        (∑' i : ℕ, sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)) / n| ≤
      R.readout () () (n : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (β := 0) le_rfl (by norm_num) (4 ^ 20) le_rfl).2.2
  change _ ≤ (-1 : ℝ) at h
  exact (not_le_of_gt (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (abs_nonneg _))) h

def family : Registration arena (type_of% @global_mesh_rate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@global_mesh_rate, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨(), (4 : ℝ) ^ (20 : ℕ), 2 * (4 : ℝ) ^ (20 : ℕ), ?_⟩
    change (1232 : ℝ) * ((4 : ℝ) ^ (20 : ℕ)) ^ (-(1 / 80 : ℝ)) ≠
      1232 * (2 * (4 : ℝ) ^ (20 : ℕ)) ^ (-(1 / 80 : ℝ))
    exact (mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow_of_neg (by positivity) (by norm_num) (by norm_num))
      (by norm_num : (0 : ℝ) < 1232)).ne'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@global_mesh_rate) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinFloors.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinFloors.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => 1232 * r ^ (-(1 / 80 : ℝ)))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinFloors
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinFloors
