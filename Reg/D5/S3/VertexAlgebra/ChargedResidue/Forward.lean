import LeanInformationAuditInterface.Contract.Registration
import Reg.D5.S3.VertexAlgebra.ChargedResidue.Locality
import D5.S3.VertexAlgebra.ChargedResidue.Forward

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.Forward
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedResidue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

abbrev forwardScope := type_of% (@chargedPhysicalResidueRow_forward)
theorem forward_source : forwardScope := @chargedPhysicalResidueRow_forward

def forwardArena : Arena where
  signature := Locality.signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ),
    (-1 : ℂ)^gamma = projectedSign epsilon →
    (-1 : ℂ)^delta = projectedSign eta →
    ∀ (K : ℕ), (bilinear D sigma tau).natAbs ≤ K → ∀ (l : ℕ) (x : ActualTensor D hu),
    observation.readout () ⟨⟨D,hu⟩,sigma,tau,epsilon,eta,gamma,delta,r,n,l⟩ x =
      ∑ k ∈ Finset.range (((K : ℤ)-r).toNat-l), Ring.choose ((gamma : ℂ)/2) k •
        chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n (l+k) x

theorem forward_bridge : forwardScope ↔ forwardArena.Law Locality.actual := Iff.rfl
theorem forward_positive : forwardArena.Law Locality.actual := forward_bridge.mp forward_source

abbrev inverseScope := type_of% (@chargedPhysicalSourceRow_inverse)
theorem inverse_source : inverseScope := @chargedPhysicalSourceRow_inverse

def sourceActual : Realization Locality.signature := realize Locality.signature (fun _ p x =>
  chargedPhysicalSourceRow p.1.val p.1.property p.2.1 p.2.2.1 p.2.2.2.1
    p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1
    p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2 x) (fun empty => nomatch empty)

def inverseArena : Arena where
  signature := Locality.signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ),
    (-1 : ℂ)^gamma = projectedSign epsilon →
    (-1 : ℂ)^delta = projectedSign eta →
    ∀ (K : ℕ), (bilinear D sigma tau).natAbs ≤ K → ∀ (x : ActualTensor D hu),
    observation.readout () ⟨⟨D,hu⟩,sigma,tau,epsilon,eta,gamma,delta,r,n,0⟩ x =
      ∑ l ∈ Finset.range (((K : ℤ)-r).toNat), Ring.choose (-(gamma : ℂ)/2) l •
        chargedPhysicalResidueRow D hu sigma tau epsilon eta gamma delta r n l x

theorem inverse_bridge : inverseScope ↔ inverseArena.Law sourceActual := Iff.rfl
theorem inverse_positive : inverseArena.Law sourceActual := inverse_bridge.mp inverse_source

/- Source scopes and positive realizations retain all original fibers.
   A complete Registration still needs the lawful enrolled-template readout,
   variation, sensitivity, observational dependence and sourceSelection. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.Forward
