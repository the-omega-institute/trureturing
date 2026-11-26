import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
import Reg.Support.DependentFamily

/-! The explicit origin error allowance varies with the cutoff. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory

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
  realize signature (fun _ _ δ => (64 / 3 : ℝ) * δ ^ (3 / 2 : ℝ)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ β a δ : ℝ, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ a → 0 ≤ δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun s => |sample β a s|) volume 0 δ ∧
        (∫ s in (0 : ℝ)..δ, |sample β a s|) ≤ R.readout () () δ) ∧
    (∀ β δ : ℝ, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ δ → δ ≤ 1 / 2 →
      IntervalIntegrable (fun s => |sample β 0 s|) volume (1 - δ) (1 + δ) ∧
        (∫ s in (1 - δ)..(1 + δ), |sample β 0 s|) ≤ 32 * δ ^ (1 / 4 : ℝ)) ∧
    (∀ β a R : ℝ, 0 ≤ β → 0 ≤ a → 2 ≤ R →
      IntegrableOn (fun s => |sample β a s|) (Set.Ioi R) ∧
        (∫ s in Set.Ioi R, |sample β a s|) ≤ 4 * R ^ (-(1 / 2 : ℝ))) ∧
    (∀ β a s : ℝ, 0 ≤ β → β ≤ 3 / 4 → 0 ≤ a → 0 < s → s ≤ 1 / 2 →
      |sample β a s| ≤ 32 * s ^ (1 / 2 : ℝ)) ∧
    (∀ β a s : ℝ, 0 ≤ β → 0 ≤ a → 2 ≤ s →
      |sample β a s| ≤ 2 * s ^ (-(3 / 2 : ℝ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law.1 0 0 0 le_rfl (by norm_num) le_rfl le_rfl (by norm_num)).2
  change (∫ s in (0 : ℝ)..0, |sample 0 0 s|) ≤ (-1 : ℝ) at h
  norm_num at h

def family : Registration arena (type_of% @mellin_cutoff_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mellin_cutoff_bounds, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1 / 2, ?_⟩
    change (64 / 3 : ℝ) * (0 : ℝ) ^ (3 / 2 : ℝ) ≠
      (64 / 3 : ℝ) * (1 / 2 : ℝ) ^ (3 / 2 : ℝ)
    rw [Real.zero_rpow (by norm_num), mul_zero]
    exact (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mellin_cutoff_bounds) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ δ => (64 / 3 : ℝ) * δ ^ (3 / 2 : ℝ))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinCutoffs
