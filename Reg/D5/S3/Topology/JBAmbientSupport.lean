import D5.S3.Topology.JBAmbientSupport
import Reg.Support.DependentFamily

/-! Whole-product dependent-family source reconstruction. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Reg.D5.S3.Topology.JBAmbientSupport
open _root_.D5.S3.Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Inputs where
  X : Type u
  [normed : NormedAddCommGroup X]
  [space : NormedSpace ℝ X]
  [complete : CompleteSpace X]
  S : X →ₗ[ℝ] X →ₗ[ℝ] X
  unit : X

attribute [instance] Inputs.normed Inputs.space Inputs.complete

abbrev signature : Signature where
  Params := Inputs.{u}
  State P := P.X × P.X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := P.X
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ P ab => P.S ab.1 ab.2) (fun e => nomatch e)

abbrev supportScope : Prop := type_of% (@JBAmbientSupport.support_of_squares.{u})
abbrev reverseScope : Prop := type_of% (@JBAmbientSupport.squares_of_supported.{u})
abbrev boundScope : Prop := type_of% (@JBAmbientSupport.corner_square_bound.{u})

abbrev supportArena : Arena where
  signature := signature.{u}
  Law r := ∀ (P : Inputs.{u}) (S : P.X →ₗ[ℝ] P.X →ₗ[ℝ] P.X),
    (∀ a b, r.readout () P (a,b) = S a b) →
    ∀ (_A : JBAlgebra.Data P.X S P.unit) (p x : P.X), S p p = p →
      ∀ c : ℝ, (∃ a : P.X, S a a = c • p + x) →
      (∃ b : P.X, S b b = c • p - x) → S p x = x

abbrev reverseArena : Arena where
  signature := signature.{u}
  Law r := ∀ (P : Inputs.{u}) (S : P.X →ₗ[ℝ] P.X →ₗ[ℝ] P.X),
    (∀ a b, r.readout () P (a,b) = S a b) →
    ∀ (_A : JBAlgebra.Data P.X S P.unit) (p x : P.X), S p p = p → S p x = x →
      (∃ a : P.X, S a a = ‖x‖ • p + x) ∧ (∃ b : P.X, S b b = ‖x‖ • p - x)

abbrev boundArena : Arena where
  signature := signature.{u}
  Law r := ∀ (P : Inputs.{u}) (S : P.X →ₗ[ℝ] P.X →ₗ[ℝ] P.X),
    (∀ a b, r.readout () P (a,b) = S a b) →
    ∀ (_A : JBAlgebra.Data P.X S P.unit) (p a : P.X), S p p = p → S p a = a →
      ∃ b : P.X, S b b = ‖a‖ ^ 2 • p - S a a

theorem support_bridge : supportScope.{u} ↔ supportArena.{u}.Law actual.{u} := by
  constructor
  · intro h P S he
    have hS : S = P.S := by
      ext a b
      exact (he a b).symm
    subst S
    exact @h P.X P.normed P.space P.complete P.S P.unit
  · intro h X normed space complete S unit
    exact h (@Inputs.mk X normed space complete S unit) S (fun _ _ => rfl)

theorem reverse_bridge : reverseScope.{u} ↔ reverseArena.{u}.Law actual.{u} := by
  constructor
  · intro h P S he
    have hS : S = P.S := by
      ext a b
      exact (he a b).symm
    subst S
    exact @h P.X P.normed P.space P.complete P.S P.unit
  · intro h X normed space complete S unit
    exact h (@Inputs.mk X normed space complete S unit) S (fun _ _ => rfl)

theorem bound_bridge : boundScope.{u} ↔ boundArena.{u}.Law actual.{u} := by
  constructor
  · intro h P S he
    have hS : S = P.S := by
      ext a b
      exact (he a b).symm
    subst S
    exact @h P.X P.normed P.space P.complete P.S P.unit
  · intro h X normed space complete S unit
    exact h (@Inputs.mk X normed space complete S unit) S (fun _ _ => rfl)

theorem support_every_readout (r : Realization signature.{u}) : supportArena.Law r := by
  intro P S _he A p x hp c hplus hminus
  exact JBAmbientSupport.support_of_squares A p x hp c hplus hminus

theorem reverse_every_readout (r : Realization signature.{u}) : reverseArena.Law r := by
  intro P S _he A p x hp hx
  exact JBAmbientSupport.squares_of_supported A p x hp hx

theorem bound_every_readout (r : Realization signature.{u}) : boundArena.Law r := by
  intro P S _he A p a hp ha
  exact JBAmbientSupport.corner_square_bound A p a hp ha

theorem support_registration_obstruction :
    ¬ Nonempty (Registration supportArena.{u} supportScope.{u}) := by
  rintro ⟨r⟩
  obtain ⟨bad, hbad⟩ := r.variation.2
  exact hbad (support_every_readout bad)

theorem reverse_registration_obstruction :
    ¬ Nonempty (Registration reverseArena.{u} reverseScope.{u}) := by
  rintro ⟨r⟩
  obtain ⟨bad, hbad⟩ := r.variation.2
  exact hbad (reverse_every_readout bad)

theorem bound_registration_obstruction :
    ¬ Nonempty (Registration boundArena.{u} boundScope.{u}) := by
  rintro ⟨r⟩
  obtain ⟨bad, hbad⟩ := r.variation.2
  exact hbad (bound_every_readout bad)

end Reg.D5.S3.Topology.JBAmbientSupport
