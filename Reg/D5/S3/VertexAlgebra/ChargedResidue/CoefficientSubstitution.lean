import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.CoefficientSubstitution

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.CoefficientSubstitution
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries

abbrev Parameters := (PowerSeries ℂ) × (PowerSeries ℂ)ˣ × ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => Unit) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p _ => coeff p.2.2 (p.1.subst (X*(p.2.1 : PowerSeries ℂ)) *
    (((p.2.1⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(p.2.2+1)) *
    derivative (X*(p.2.1 : PowerSeries ℂ)))) (fun empty => nomatch empty)

abbrev coefficientScope := type_of% (@coeff_subst_jacobian)
theorem coefficient_source : coefficientScope := @coeff_subst_jacobian

def coefficientArena : Arena where
  signature := signature
  Law observation := ∀ (f : PowerSeries ℂ) (u : (PowerSeries ℂ)ˣ) (n : ℕ),
    observation.readout () ⟨f,u,n⟩ () = coeff n f

theorem coefficient_bridge : coefficientScope ↔ coefficientArena.Law actual := Iff.rfl
theorem coefficient_positive : coefficientArena.Law actual := coefficient_bridge.mp coefficient_source

/- These exact source scopes and positive realizations retain the original
   infinite parameter and series families. Registration still needs a lawful
   enrolled-template readout, whole-family variation, sensitivity, observational
   dependence and structural sourceSelection; none is inferred from positivity. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.CoefficientSubstitution
