import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.VertexAlgebra.ChargedResidue.Locality
import D5.S3.VertexAlgebra.ChargedResidue.JointDiagonal

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.JointDiagonal
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockPhysicalRescaling
open LatticeHalfFockChargedResidue LatticeHalfFockProductKernel LatticeHalfFockChargedCoefficients
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct VertexOperator

abbrev sourceScope := type_of% (@chargedPhysicalResidueRow_joint_native)
theorem source_actual : sourceScope := @chargedPhysicalResidueRow_joint_native

def arena : Arena where
  signature := Locality.signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ),
    (-1 : ℂ)^gamma = projectedSign epsilon →
    (-1 : ℂ)^delta = projectedSign eta →
    ∀ (l : ℕ) (p : Oscillator D) (g : ActualGround D hu),
    let A := physicalSlice D hu (chargedField D hu sigma) gamma
    let B := physicalSlice D hu (chargedField D hu tau) delta
    let forward := (-(n-l)-((HahnModule.of ℂ).symm (B (p ⊗ₜ[ℂ] g))).order).toNat
    let reverse := (-((HahnModule.of ℂ).symm (A (p ⊗ₜ[ℂ] g))).order).toNat
    observation.readout () ⟨⟨D, hu⟩, sigma, tau, epsilon, eta, gamma, delta, r, n, l⟩
        (p ⊗ₜ[ℂ] g) =
      (chargeScalar D sigma * chargeScalar D tau) •
        ((∑ d ∈ (pairTranslation D sigma tau p).support,
          (pairTranslation D sigma tau p).coeff d *
            nativeJointDiagonal D sigma tau gamma delta (r+l) (n-l) forward reverse d)
              ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g))

theorem source_bridge : sourceScope ↔ arena.Law Locality.actual := Iff.rfl
theorem actual_positive : arena.Law Locality.actual := source_bridge.mp source_actual

/- The full original telescope has an exact source bridge and positive
   realization. Whole-family variation, sensitivity, observational dependence
   and structural sourceSelection remain additional Registration targets. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.JointDiagonal
