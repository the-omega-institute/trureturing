import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.QuadraticResidue

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.QuadraticResidue
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries

abbrev Parameters := ℤ × ℤ × ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => Unit) (fun _ => ℂ)

def actual : Realization signature := realize signature
  (fun _ p _ => collisionScalar p.1 p.2.1 p.2.2) (fun empty => nomatch empty)

abbrev jacobianScope := type_of% (@collision_scalar_jacobian)
theorem jacobian_source : jacobianScope := @collision_scalar_jacobian

def jacobianArena : Arena where
  signature := signature
  Law observation := ∀ (a B : ℤ) (N : ℕ),
    observation.readout () ⟨a,B,N⟩ () = coeff N
      (binomialSeries (R := ℤ) ℂ a *
        ((normalizedCoordinateUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        (((quadraticCoordinateUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(N+1)) *
        (2*(1+X)))

theorem jacobian_bridge : jacobianScope ↔ jacobianArena.Law actual := Iff.rfl
theorem jacobian_positive : jacobianArena.Law actual := jacobian_bridge.mp jacobian_source

abbrev coordinateScope := type_of% (@collision_scalar_coordinate)
theorem coordinate_source : coordinateScope := @collision_scalar_coordinate

def coordinateArena : Arena where
  signature := signature
  Law observation := ∀ (a B : ℤ) (N : ℕ),
    observation.readout () ⟨a,B,N⟩ () = (2 : ℂ)^(2*B+1) *
      coeff N (binomialSeries (R := ℤ) ℂ (a+1) *
        ((quadraticCoordinateUnit ^ (-2*B-(N : ℤ)-1) : (PowerSeries ℂ)ˣ) :
          PowerSeries ℂ))

theorem coordinate_bridge : coordinateScope ↔ coordinateArena.Law actual := Iff.rfl
theorem coordinate_positive : coordinateArena.Law actual := coordinate_bridge.mp coordinate_source

/- These exact source scopes and positive realizations retain the original
   infinite parameter and series families. Registration still needs a lawful
   enrolled-template readout, whole-family variation, sensitivity, observational
   dependence and structural sourceSelection; none is inferred from positivity. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.QuadraticResidue
