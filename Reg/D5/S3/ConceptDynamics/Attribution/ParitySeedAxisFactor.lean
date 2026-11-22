import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Σ n : ℕ, ℕ × Fin (n + 2)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p budget => axisFactorWithin p.2.1 p.2.2 budget)
    (fun e => nomatch e)

def alwaysFalse : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (_even : (n + 2) % 2 = 0), k % 2 = 1 →
    ∀ (i : Fin (n + 2)) (budget : ℕ),
      (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧
        (∀ j, z j ≤ if j = i then budget else 0)) ↔
        R.readout () ⟨n, k, i⟩ budget

private theorem first_only : RealizableSeedCounts 0 1 ![4, 0] :=
  (exact_two_coordinate_counts 1 _).2 ⟨1, 0, by decide, by decide, by decide⟩

private theorem fits_first : ∀ j : Fin 2, ![4, 0] j ≤ if j = 0 then 4 else 0 := by
  decide

private theorem zero_impossible :
    ¬ ∃ z : Fin 2 → ℕ, RealizableSeedCounts 0 1 z ∧ ∀ j, z j ≤ (if j = 0 then 0 else 0) := by
  rintro ⟨z, feasible, cap⟩
  have zero : z = fun _ => 0 := funext fun j => Nat.eq_zero_of_le_zero (by simpa using cap j)
  rw [zero] at feasible
  exact (by decide : ¬ (Odd (0 + 2) ∨ Even 1)) ((zero_coordinate_counts_iff 0 1).mp feasible)

private theorem always_false_fails : ¬ arena.Law alwaysFalse := by
  intro law
  exact (law 0 1 rfl rfl 0 4).mp ⟨_, first_only, fits_first⟩

def family : Registration arena (type_of% axis_budget_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨axis_budget_iff, alwaysFalse, always_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨alwaysFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, always_false_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨0, 1, 0⟩, 0, 4, ?_⟩
    have noSupport : ¬ axisFactorWithin 1 (0 : Fin 2) 0 :=
      fun h => zero_impossible ((axis_budget_iff 0 1 rfl rfl 0 0).mpr h)
    have support : axisFactorWithin 1 (0 : Fin 2) 4 :=
      (axis_budget_iff 0 1 rfl rfl 0 4).mp ⟨_, first_only, fits_first⟩
    simp [actual, realize, noSupport, support]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    axis_budget_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor.coordinateBudget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p budget => axisFactorWithin p.2.1 p.2.2 budget)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
