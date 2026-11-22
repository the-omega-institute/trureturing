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
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def threshold (limit : ℕ) : Realization signature :=
  realize signature (fun _ _ budget => decide (limit ≤ budget)) (fun a => nomatch a)

private def constantFalse : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

private abbrev fullArena : Arena where
  signature := signature
  Law R := ∀ budget : ℕ, axisFactorWithin 3 (0 : Fin 16) budget ↔
    R.readout () () budget = true

private theorem full_false_fails : ¬ fullArena.Law constantFalse := by
  intro law
  have feasible := (full_budget_iff 2036).2 (by decide)
  exact Bool.false_ne_true ((law 2036).mp feasible)

def fullFamily : Registration fullArena (type_of% full_budget_iff) where
  actual := threshold 2036
  bridge := by simp [threshold, realize]
  variation := ⟨by simpa [fullArena, threshold, realize] using full_budget_iff,
    constantFalse, full_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨constantFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, full_false_fails⟩
    · intro a
      exact nomatch a
  dependence := by
    rintro ⟨⟩
    exact ⟨(), 2035, 2036, by decide⟩

def fullRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    full_budget_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen.fullBudget
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen.fullFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fullArena⟩
  objectArena := .source ⟨fullArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fullArena ⟨fullFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ budget => decide (2036 ≤ budget)) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.DimensionSixteen
