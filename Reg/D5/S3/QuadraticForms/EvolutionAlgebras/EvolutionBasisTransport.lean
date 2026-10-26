import D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport

open _root_.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

abbrev signature : Signature where
  Params := Unit
  State _ := A →ₗ[ℂ] A →ₗ[ℂ] A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Submodule ℂ B
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual (e : A ≃ₗ[ℂ] B) : Realization (signature (A := A) (B := B)) :=
  realize signature (fun _ _ μ => (productSpan μ).map e.toLinearMap) (fun a => nomatch a)

abbrev arena (e : A ≃ₗ[ℂ] B) : Arena where
  signature := signature (A := A) (B := B)
  Law R := ∀ (μ : A →ₗ[ℂ] A →ₗ[ℂ] A),
    R.readout () () μ = productSpan (transportProduct e μ)

theorem actual_law (e : A ≃ₗ[ℂ] B) : (arena e).Law (actual e) := by
  intro μ
  exact product_span_transport e μ

/-- A fixed degenerate carrier cannot support observational dependence in this candidate arena.
A registration of the unrestricted source theorem must put carriers in the parameter family. -/
theorem fixed_carrier_obstruction [Subsingleton B] (e : A ≃ₗ[ℂ] B) :
    ¬ ObservationalDependence (signature (A := A) (B := B)) (actual e) := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy (Subsingleton.elim _ _)

end Reg.D5.S3.QuadraticForms.EvolutionAlgebras.EvolutionBasisTransport
