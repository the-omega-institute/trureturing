import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse

open _root_.D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u
noncomputable section

/-- Observe the prescribed AB phase coefficient in the zero-mixing criterion. -/
abbrev signature : Signature where
  Params := Type u
  State K := K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ K := K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ β => β) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {K : Type u} [Field K] (T : Set K) (_ : ∀ t ∈ T, t * t ≠ 1)
    (β γ ε ζ : K),
    (∃ t ∈ T, ∃ a b d e f : K,
      β = -b * d * t ∧ γ = -d * (e + t * f) ∧
      ε = -a * (e + t * f) ∧ ζ = -b * (t * e + f)) ↔
    (0 ∈ T ∧ r.readout () K β = 0) ∨
    ((∃ t ∈ T, t ≠ 0) ∧
      (β ≠ 0 ∨ γ = 0 ∨ ζ = 0) ∧ (γ ≠ 0 ∨ β = 0 ∨ ε = 0))

/-- Change the readout whenever the carrier supplies a different coefficient. -/
def intervention : Realization signature.{u} := by
  classical
  exact realize signature
    (fun _ K β => if h : ∃ x : K, x ≠ β then Classical.choose h else β)
    (fun e => nomatch e)

private theorem intervention_fails : ¬ arena.{u}.Law intervention := by
  intro law
  let T : Set (ULift.{u} ℚ) := {t | t = 0}
  have hT : ∀ t ∈ T, t * t ≠ 1 := by
    intro t ht
    change t = 0 at ht
    simp [ht]
  have h₀ : (0 : ULift.{u} ℚ) ∈ T := rfl
  rcases (law T hT 0 0 0 0).mp ⟨0, h₀, 0, 0, 0, 0, 0, by simp⟩ with
    ⟨_, hr⟩ | ⟨⟨t, ht, hne⟩, _⟩
  · have h : ∃ x : ULift.{u} ℚ, x ≠ 0 := ⟨1, one_ne_zero⟩
    classical
    change (if hx : ∃ x : ULift.{u} ℚ, x ≠ 0 then Classical.choose hx else 0) = 0 at hr
    rw [dite_eq_left h] at hr
    exact Classical.choose_spec h hr
  · exact hne ht

def sourceRegistration : Registration arena.{u} (type_of% @response_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨response_iff, intervention, intervention_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨intervention, ?_, rfl, intervention_fails⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨ULift.{u} ℚ, 0, 1, zero_ne_one⟩

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@response_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨sourceRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ β => β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.Quantum.Matrix.Schur.TwoHiddenScalarResponse
