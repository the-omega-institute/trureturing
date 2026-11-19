import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching
import Reg.Support.DependentFamily

/-! Dependent-family registration of the mechanical path-cost bound. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.PrimitivePayoffSwitching

set_option autoImplicit false

namespace Reg.D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching

noncomputable section

abbrev costSignature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℕ, ℕ
  State parameters := Response parameters.2.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualCost : Realization costSignature :=
  realize costSignature
    (fun _ parameters p =>
      cost parameters.1
        (mechanicalWindow parameters.1 parameters.2.1 parameters.2.2.2 parameters.2.2.1) p)
    (fun e => nomatch e)

def rejectedCost : Realization costSignature :=
  realize costSignature (fun _ _ _ => -2) (fun e => nomatch e)

def boundaryArena : Arena where
  signature := costSignature
  Law r := ∀ {α ρ : ℝ} (_ : 0 ≤ α) (_ : α < 1) {n : ℕ} (start : ℕ) (p : Response n),
    sgn (p 0) * potential α ρ start - sgn (p (Fin.last n)) * potential α ρ (start + n) ≤
      r.readout () ⟨α, ρ, n, start⟩ p

private theorem rejection_breaks_boundary : ¬ boundaryArena.Law rejectedCost := by
  intro h
  have hbad := @h 0 0 (by norm_num) (by norm_num) 1 0 (fun _ => true)
  change sgn true * potential 0 0 0 - sgn true * potential 0 0 (0 + 1) ≤ (-2 : ℝ) at hbad
  norm_num [potential, sgn, Int.fract_zero] at hbad

private theorem actual_cost_depends_on_path :
    ObservationalDependence costSignature actualCost := by
  intro _
  let loop : Response 1 := fun _ => true
  let switch : Response 1 := fun i => decide (i.val = 0)
  refine ⟨⟨0, 0, 1, 0⟩, loop, switch, ?_⟩
  intro heq
  let b := mechanicalWindow 0 0 0 1 (0 : Fin 1)
  change cost 0 (mechanicalWindow 0 0 0 1) loop =
    cost 0 (mechanicalWindow 0 0 0 1) switch at heq
  simp only [cost, Fin.sum_univ_one] at heq
  change payoff 0 b true true = payoff 0 b true false at heq
  norm_num [payoff, sgn, switchCost] at heq

def boundaryFamily :
    Registration boundaryArena (type_of% (@mechanical_cost_ge_boundary)) where
  actual := actualCost
  bridge := Iff.rfl
  variation := ⟨@mechanical_cost_ge_boundary, rejectedCost, rejection_breaks_boundary⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCost, ?_, rfl, rejection_breaks_boundary⟩
      intro j h
      have sameRole : (j : Unit) = (i : Unit) := @Subsingleton.elim Unit inferInstance j i
      exact (h sameRole).elim
    · intro e
      exact nomatch e
  dependence := actual_cost_depends_on_path

def boundaryRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mechanical_cost_ge_boundary) (Realization costSignature) Unit Unit where
  unitName := `Reg.D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching.boundaryUnit
  realizationName := `Reg.D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching.boundaryFamily
  realizationSource := none
  generated := false
  arena := .source ⟨boundaryArena⟩
  objectArena := .source ⟨boundaryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source boundaryArena ⟨boundaryFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize costSignature
    (fun _ parameters p =>
      cost parameters.1
        (mechanicalWindow parameters.1 parameters.2.1 parameters.2.2.2 parameters.2.2.1) p)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Dynamics.Symbolic.PrimitivePayoffSwitching
