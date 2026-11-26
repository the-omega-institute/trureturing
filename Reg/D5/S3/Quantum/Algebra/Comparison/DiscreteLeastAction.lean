import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction
import Reg.Support.DependentFamily

/-! Source-bound audit of the finite cosine action. -/

namespace Reg.D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction

open _root_.D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction (sum_one_sub_cos_least_action)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Real
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ ι : Type u, Fintype ι
  State p := p.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p t => by
    letI := p.2
    exact ∑ i, (1 - cos (t i))) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {ι : Type u} [Fintype ι] (t : ι → ℝ) (θ : ℝ),
    (∀ i, 0 ≤ t i) → (∑ i, t i = θ) → θ ≤ π →
    (Fintype.card ι : ℝ) * (1 - cos (θ / Fintype.card ι)) ≤
        R.readout () ⟨ι, inferInstance⟩ t ∧
      ((∑ i, (1 - cos (t i))) = (Fintype.card ι : ℝ) * (1 - cos (θ / Fintype.card ι)) ↔
        (∀ i, t i = θ / Fintype.card ι) ∨ Fintype.card ι = 2 ∧ θ = π)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hle := (h (fun _ : ULift.{u} Unit => π) π
    (fun _ => Real.pi_pos.le) (by simp) le_rfl).1
  norm_num [rejected, realize, Real.cos_pi] at hle

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, fun _ => 0, fun _ => π, ?_⟩
  norm_num [actual, realize, Real.cos_pi]

def source_registration : Registration arena.{u}
    (type_of% @sum_one_sub_cos_least_action.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_one_sub_cos_least_action.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_one_sub_cos_least_action.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := .str
    `D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction.sum_one_sub_cos_least_action
    "__information_unit"
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p t => by
    letI := p.2
    exact ∑ i, (1 - cos (t i))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Algebra.Comparison.DiscreteLeastAction
