import D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature (parameters : Type := Unit) : Signature where
  Params := parameters
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def threshold {parameters : Type} (limit : ℕ) : Realization (signature parameters) :=
  realize (signature parameters) (fun _ _ budget => decide (limit ≤ budget)) (fun a => nomatch a)

private def constantFalse {parameters : Type} : Realization (signature parameters) :=
  realize (signature parameters) (fun _ _ _ => false) (fun a => nomatch a)

private abbrev coverArena : Arena where
  signature := signature
  Law R := ∀ budget : ℕ, coverWithin budget → R.readout () () budget = true

private theorem some_cover_budget : ∃ budget, coverWithin budget := by
  let i : Fin 16 := 0
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
    · have h' : b ≠ a := fun he => h he.symm
      simp [edge, h, h']
  have degree_ok (a : AxisSubset 16 i) :
      residualDegree 3 true (decide (a = axisTop i)) (∑ b, (edge a b).toNat) := by
    rw [degree]
    by_cases ha : a = axisTop i <;> simp [ha, residualDegree]
  refine ⟨axisCost i edge, edge, true, ?_, by simp, degree_ok, ?_, ?_, le_rfl⟩
  · change edge (axisTop i) (axisTop i) = false
    simp [edge]
  · intro b
    simpa only [symm b] using degree_ok b
  · intro a b _ h
    have he : a = b := (of_decide_eq_true h).1
    subst b
    exact ⟨Subset.rfl, Or.inl rfl⟩

private theorem cover_false_fails : ¬ coverArena.Law constantFalse := by
  intro law
  obtain ⟨budget, feasible⟩ := some_cover_budget
  exact Bool.false_ne_true (law budget feasible)

def coverFamily : Registration coverArena (type_of% cover_budget_ge) where
  actual := threshold 2044
  bridge := by simp [threshold, realize]
  variation := ⟨by simpa [coverArena, threshold, realize] using cover_budget_ge,
    constantFalse, cover_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨constantFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, cover_false_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 2043, 2044, by decide⟩

def coverRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    cover_budget_ge (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers.coverBudget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers.coverFamily
  realizationSource := none
  generated := false
  arena := .source ⟨coverArena⟩
  objectArena := .source ⟨coverArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coverArena ⟨coverFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ budget => decide (2044 ≤ budget)) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev fullLowerArena : Arena where
  signature := signature (Fin 16)
  Law R := ∀ (i : Fin 16) (budget : ℕ),
    axisFactorWithin 3 i budget → R.readout () i budget = true

private theorem full_lower_false_fails : ¬ fullLowerArena.Law constantFalse := by
  intro law
  obtain ⟨budget, edge, selected, omitted, permitted, rows, cols, support, cost⟩ := some_cover_budget
  have feasible : axisFactorWithin 3 (0 : Fin 16) budget :=
    ⟨edge, selected, omitted, permitted, rows, cols, fun a b ha hb => (support a b ha hb).1, cost⟩
  exact Bool.false_ne_true (law 0 budget feasible)

def fullLowerFamily : Registration fullLowerArena (type_of% full_budget_ge) where
  actual := threshold 2036
  bridge := by simp [threshold, realize]
  variation := ⟨by simpa [fullLowerArena, threshold, realize] using full_budget_ge,
    constantFalse, full_lower_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨constantFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, full_lower_false_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    rintro ⟨⟩
    exact ⟨0, 2035, 2036, by decide⟩

def fullLowerRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    full_budget_ge (Realization (signature (Fin 16))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers.fullBudgetLower
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers.fullLowerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fullLowerArena⟩
  objectArena := .source ⟨fullLowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullLowerArena ⟨fullLowerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (signature (Fin 16))
    (fun _ _ budget => decide (2036 ≤ budget)) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers
    definition := none
    coordinates := #[]
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
end Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteenCovers
