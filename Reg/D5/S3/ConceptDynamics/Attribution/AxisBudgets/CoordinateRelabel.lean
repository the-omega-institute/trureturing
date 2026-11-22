import D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Observe feasibility as the budget varies at the source marked coordinate. -/

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel

open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedFactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev Params := Σ d : ℕ, Σ _ : Fin d, Σ _ : Fin d, ℕ

private abbrev signature : Signature where
  Params := Params
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def feasible (p : Params) (budget : ℕ) : Prop :=
  axisFactorWithin p.2.2.2 p.2.1 budget

private def readFeasible (p : Params) (budget : ℕ) : Bool :=
  @decide (feasible p budget) (Classical.propDecidable _)

private def actual : Realization signature :=
  realize signature (fun _ p budget => readFeasible p budget) (fun a => nomatch a)

private def alwaysFeasible : Realization signature :=
  realize signature (fun _ _ _ => true) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} (i j : Fin d) (k budget : ℕ),
    R.readout () ⟨d, i, j, k⟩ budget = true ↔ axisFactorWithin k j budget

private theorem readFeasible_spec (p : Params) (budget : ℕ) :
    readFeasible p budget = true ↔ feasible p budget := by
  simp only [readFeasible, decide_eq_true_eq]

private theorem tooSmall {d : ℕ} (i : Fin d) (k : ℕ) : ¬ axisFactorWithin k i 0 := by
  rintro ⟨f, _, _, _, _, _, _, cost⟩
  unfold axisCost at cost
  omega

private theorem alwaysFeasible_fails : ¬ arena.Law alwaysFeasible := by
  intro law
  exact tooSmall (0 : Fin 1) 3 ((law 0 0 3 0).mp rfl)

private theorem oneCoordinate : axisFactorWithin 3 (0 : Fin 1) 4 := by
  have topOnly (A : AxisSubset 1 (0 : Fin 1)) : A = axisTop 0 := by
    apply Subtype.ext
    ext j
    fin_cases j
    simp [axisTop, A.property]
  refine ⟨fun _ _ => false, true, rfl, by simp, ?_, ?_, by simp, ?_⟩
  · intro A
    simp [topOnly A, residualDegree]
  · intro A
    simp [topOnly A, residualDegree]
  · simp [axisCost, topOnly]

def family : Registration arena (type_of% @axis_feasibility_iff) where
  actual := actual
  bridge := by
    change _ ↔ (∀ {d : ℕ} (i j : Fin d) (k budget : ℕ),
      readFeasible ⟨d, i, j, k⟩ budget = true ↔ axisFactorWithin k j budget)
    simp only [readFeasible_spec, feasible]
  variation := ⟨by
    intro d i j k budget
    exact (readFeasible_spec ⟨d, i, j, k⟩ budget).trans (axis_feasibility_iff i j k budget),
    alwaysFeasible, alwaysFeasible_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨alwaysFeasible, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, alwaysFeasible_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    intro role
    refine ⟨⟨1, 0, 0, 3⟩, 0, 4, ?_⟩
    change readFeasible ⟨1, 0, 0, 3⟩ 0 ≠ readFeasible ⟨1, 0, 0, 3⟩ 4
    intro equal
    have yes := (readFeasible_spec ⟨1, 0, 0, 3⟩ 4).mpr oneCoordinate
    exact tooSmall (0 : Fin 1) 3 ((readFeasible_spec _ 0).mp (equal.trans yes))

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@axis_feasibility_iff) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel.coordinateBudget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p budget => @decide (axisFactorWithin p.2.2.2 p.2.1 budget) (Classical.propDecidable _))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.CoordinateRelabel
