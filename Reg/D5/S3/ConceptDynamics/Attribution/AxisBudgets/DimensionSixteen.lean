import D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Fin 16
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ budget => decide (2036 ≤ budget)) (fun a => nomatch a)

def constantFalse : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (i : Fin 16) (budget : ℕ), axisFactorWithin 3 i budget →
    R.readout () i budget = true

private theorem some_budget (i : Fin 16) : ∃ budget, axisFactorWithin 3 i budget := by
  let edge (a b : AxisSubset 16 i) := decide (a = b ∧ a ≠ axisTop i)
  have degree (a : AxisSubset 16 i) :
      (∑ b, (edge a b).toNat) = if a = axisTop i then 0 else 1 := by
    by_cases ha : a = axisTop i
    · simp [edge, ha]
    · rw [sum_eq_single a]
      · simp [edge, ha]
      · intro b _ hba
        simp [edge, hba.symm]
      · simp
  have symm (a b : AxisSubset 16 i) : edge a b = edge b a := by
    by_cases h : a = b
    · subst b
      rfl
    · simp [edge, h, h.symm]
  have degree_ok (a : AxisSubset 16 i) :
      residualDegree 3 true (decide (a = axisTop i)) (∑ b, (edge a b).toNat) := by
    rw [degree]
    by_cases ha : a = axisTop i <;> simp [ha, residualDegree]
  refine ⟨axisCost i edge, edge, true, by simp [edge], by simp, degree_ok, ?_, ?_, le_rfl⟩
  · intro b
    simpa only [symm b] using degree_ok b
  · intro a b _ h
    have he : a = b := (of_decide_eq_true h).1
    subst b
    exact Subset.rfl

private theorem constant_false_fails : ¬ arena.Law constantFalse := by
  intro law
  obtain ⟨budget, feasible⟩ := some_budget 0
  exact Bool.false_ne_true (law 0 budget feasible)

def family : Registration arena (type_of% axis_budget_ge_2036) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using axis_budget_ge_2036,
    constantFalse, constant_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨constantFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, constant_false_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    rintro ⟨⟩
    exact ⟨0, 2035, 2036, by decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    axis_budget_ge_2036 (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen.budget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ budget => decide (2036 ≤ budget)) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen
