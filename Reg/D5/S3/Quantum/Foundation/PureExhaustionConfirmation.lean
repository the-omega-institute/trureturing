import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Foundation.PureExhaustionConfirmation
import Reg.Support.DependentFamily

noncomputable section
universe u
open scoped BigOperators

namespace Reg.D5.S3.Quantum.Foundation.PureExhaustionConfirmation

open _root_.D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
open _root_.D5.S3.Quantum.Foundation.PureExhaustionConfirmation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  A : Type u
  [add : NormedAddCommGroup A]
  [space : NormedSpace ℝ A]
  [finite : FiniteDimensional ℝ A]
  cone : PointedCone ℝ A
  unit : A →ₗ[ℝ] ℝ

attribute [instance] Inputs.add Inputs.space Inputs.finite

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.A × P.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ P : Inputs.{u},
    let C := P.cone
    let u := P.unit
    IsClosed (C : Set P.A) →
    (∀ x ∈ C, x ≠ 0 → 0 < u x) →
    Submodule.span ℝ (C : Set P.A) = ⊤ →
    ∀ p q : pure C u, purePairRelation C u p q →
      R.readout () P ((p : P.A), (q : P.A)) →
      p ≠ q ∧
      (∃ f : P.A →ₗ[ℝ] ℝ, confirms C u q f ∧ f p = 0) ∧
      (∀ x ∈ base C u, comparison C u p x + comparison C u q x = 1) ∧
      ∃ ep eq : P.A →ₗ[ℝ] ℝ,
        confirms C u p ep ∧ confirms C u q eq ∧
        (∀ f, confirms C u p f → ∀ x ∈ C, ep x ≤ f x) ∧
        (∀ f, confirms C u q f → ∀ x ∈ C, eq x ≤ f x) ∧
        (∀ x ∈ C, comparison C u p x = ep x) ∧
        (∀ x ∈ C, comparison C u q x = eq x) ∧
        ep + eq = u

abbrev sourceScope : Prop := type_of% (@pure_exhaustion_entry.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    dsimp
    intro hclosed hstrict hspan p q hrel hread
    exact @h P.A P.add P.space P.finite P.cone P.unit hclosed hstrict hspan p q hrel
  · intro h
    intro A add space finite C u hclosed hstrict hspan p q hrel
    exact h ⟨A, C, u⟩ hclosed hstrict hspan p q hrel trivial

end Reg.D5.S3.Quantum.Foundation.PureExhaustionConfirmation
