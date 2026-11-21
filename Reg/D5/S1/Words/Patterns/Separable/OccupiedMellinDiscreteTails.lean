import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails
import Reg.Support.DependentFamily

/-! The origin allowance varies with the normalized mesh cutoff. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails
open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
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
  realize signature (fun _ _ r => 32 * r ^ (3 / 2 : ℝ)) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (β a : ℝ) (n K : ℕ), 0 ≤ β → β ≤ 3 / 4 → 0 ≤ a → 0 < n →
      (K : ℝ) / n ≤ 1 / 2 →
      (∑ i ∈ Finset.range K, |sample β a ((i + 1 : ℕ) / (n : ℝ))|) / n ≤
        R.readout () () ((K : ℝ) / n)) ∧
    (∀ (β a : ℝ) (n M : ℕ), 0 ≤ β → 0 ≤ a → 0 < n → 2 ≤ (M : ℝ) / n →
      Summable (fun i : ℕ => |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|) ∧
        (∑' i : ℕ, |sample β a ((M + i + 1 : ℕ) / (n : ℝ))|) / n ≤
          4 * ((M : ℝ) / n) ^ (-(1 / 2 : ℝ)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := law.1 0 0 1 0 le_rfl (by norm_num) le_rfl (by decide) (by norm_num)
  change _ ≤ (-1 : ℝ) at h
  norm_num at h

def family : Registration arena (type_of% @discrete_mellin_tail_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨discrete_mellin_tail_bounds, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1 / 2, ?_⟩
    change (32 : ℝ) * (0 : ℝ) ^ (3 / 2 : ℝ) ≠
      32 * (1 / 2 : ℝ) ^ (3 / 2 : ℝ)
    rw [Real.zero_rpow (by norm_num), mul_zero]
    exact (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)).ne

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@discrete_mellin_tail_bounds) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => 32 * r ^ (3 / 2 : ℝ))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinDiscreteTails
