import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParitySeedForest
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedForest

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedForest
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State p := Fin (p.1 + 2) → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p budget => decide (forestSupportWithin p.1 p.2 budget))
    (fun e => nomatch e)

def alwaysFalse : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ) (_even : (n + 2) % 2 = 0), k % 2 = 1 →
    ∀ budget : Fin (n + 2) → ℕ,
      (∃ z : Fin (n + 2) → ℕ, RealizableSeedCounts n k z ∧ ∀ i, z i ≤ budget i) ↔
        R.readout () ⟨n, k⟩ budget = true

private theorem first_only : RealizableSeedCounts 0 1 ![4, 0] :=
  (exact_two_coordinate_counts 1 _).2 ⟨1, 0, by decide, by decide, by decide⟩

private theorem zero_impossible :
    ¬ ∃ z : Fin 2 → ℕ, RealizableSeedCounts 0 1 z ∧ ∀ i, z i ≤ 0 := by
  rintro ⟨z, feasible, cap⟩
  have zero : z = fun _ => 0 := funext fun i => Nat.eq_zero_of_le_zero (cap i)
  rw [zero] at feasible
  exact (by decide : ¬ (Odd (0 + 2) ∨ Even 1)) ((zero_coordinate_counts_iff 0 1).mp feasible)

private theorem always_false_fails : ¬ arena.Law alwaysFalse := by
  intro law
  exact Bool.false_ne_true ((law 0 1 rfl rfl ![4, 0]).mp ⟨_, first_only, fun _ => le_rfl⟩)

def family : Registration arena (type_of% forest_support_iff) where
  actual := actual
  bridge := by simp [actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using forest_support_iff,
    alwaysFalse, always_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨alwaysFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, always_false_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨0, 1⟩, fun _ => 0, ![4, 0], ?_⟩
    have noSupport : ¬ forestSupportWithin 0 1 (fun _ => 0) :=
      fun h => zero_impossible ((forest_support_iff 0 1 rfl rfl _).mpr h)
    have support : forestSupportWithin 0 1 ![4, 0] :=
      (forest_support_iff 0 1 rfl rfl _).mp ⟨_, first_only, fun _ => le_rfl⟩
    simp [actual, realize, noSupport, support]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    forest_support_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedForest.coordinateBudget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedForest.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p budget =>
    decide (forestSupportWithin p.1 p.2 budget)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedForest
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedForest
