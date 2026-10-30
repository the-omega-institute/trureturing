import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.SourceToQ

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.SourceToQ
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedResidue
open LatticeHalfFockGroundRightCurrentTransport LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling Calculus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  sigma : Charge D
  tau : Charge D
  epsilon : Bool
  eta : Bool
  gamma : ℤ
  delta : ℤ
  r : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => Unit) (fun p => VertexOperator ℂ (ActualTensor p.D p.hu))

def actual : Realization signature := realize signature (fun _ p _ =>
  physicalSlice p.D p.hu (correctedField p.D p.hu
    (chargedGroundSource p.D p.sigma p.tau p.epsilon p.eta p.r)) (p.gamma+p.delta))
  (fun empty => nomatch empty)

abbrev fieldScope := type_of% (@chargedGroundSource_to_Q)
theorem field_source : fieldScope := @chargedGroundSource_to_Q

def fieldArena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r : ℤ),
    (-1 : ℂ)^gamma = projectedSign epsilon →
    (-1 : ℂ)^delta = projectedSign eta →
    ∀ (K : ℕ), (bilinear D sigma tau).natAbs ≤ K →
    observation.readout () ⟨D,hu,sigma,tau,epsilon,eta,gamma,delta,r⟩ () =
      Q (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
        (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta) gamma r K

theorem field_bridge : fieldScope ↔ fieldArena.Law actual := Iff.rfl
theorem field_positive : fieldArena.Law actual := field_bridge.mp field_source

abbrev sectorScope := type_of% (@charged_sector_ground_pair)
theorem sector_source : sectorScope := @charged_sector_ground_pair

def sectorArena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta : ℤ),
    sectorSign epsilon = (-1 : ℂ)^gamma → sectorSign eta = (-1 : ℂ)^delta →
    fullLaw
      (physicalSlice D hu (correctedField D hu (projectedGround D sigma epsilon)) gamma)
      (physicalSlice D hu (correctedField D hu (projectedGround D tau eta)) delta)
      (fun r => observation.readout () ⟨D,hu,sigma,tau,epsilon,eta,gamma,delta,r⟩ ()) gamma

theorem sector_bridge : sectorScope ↔ sectorArena.Law actual := Iff.rfl
theorem sector_positive : sectorArena.Law actual := sector_bridge.mp sector_source

/- The actual source reconstruction and full original telescope are retained.
   A Contract.Registration remains unproved: lawful enrolled-template readout,
   whole-family variation, sensitivity, observational dependence and structural
   sourceSelection are required; positivity alone supplies none of these. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.SourceToQ
