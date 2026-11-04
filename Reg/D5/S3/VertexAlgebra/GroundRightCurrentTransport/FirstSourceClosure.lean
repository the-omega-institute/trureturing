import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGroundRightCurrentTransport LatticeFiniteNegativeGeneration
open LatticeAllStateReconstruction Calculus
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

structure Parameters where
  D : LatticeData
  hu : IsUnit D.G.det
  a : Carrier D
  gamma : ℤ
  b : Carrier D
  delta : ℤ
  r : ℤ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun _ => Unit) (fun p => VertexOperator ℂ (ActualTensor p.D p.hu))

def actual : Realization signature := realize signature (fun _ p _ =>
  LatticeHalfFockLeftCurrentTransport.targetSlice p.D p.hu
    (mu p.D p.a p.r p.b) (p.gamma+p.delta)) (fun empty => nomatch empty)

abbrev firstScope := type_of% (@first_eigen_arbitrary_second)
theorem first_source : firstScope := @first_eigen_arbitrary_second

def firstArena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (a : Carrier D) (gamma : ℤ),
    LatticeInvolution.theta D a = (-1 : ℂ)^gamma • a →
    ∀ (b : Carrier D) (delta : ℤ),
      fullLaw (LatticeHalfFockLeftCurrentTransport.targetSlice D hu a gamma)
        (LatticeHalfFockLeftCurrentTransport.targetSlice D hu b delta)
        (fun r => observation.readout () ⟨D,hu,a,gamma,b,delta,r⟩ ()) gamma

theorem first_bridge : firstScope ↔ firstArena.Law actual := Iff.rfl
theorem first_positive : firstArena.Law actual := first_bridge.mp first_source

abbrev stepScope := type_of% (@first_current_step)
theorem step_source : stepScope := @first_current_step

def stepArena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a : Carrier D) (gamma : ℤ),
    (∀ b : Carrier D, ∀ delta : ℤ, OriginalCompatible D hu a b gamma delta) →
    ∀ (d : ℤ) (b : Carrier D) (delta : ℤ),
      fullLaw
        (LatticeHalfFockLeftCurrentTransport.targetSlice D hu (neutralMode D i d a) (gamma+1))
        (LatticeHalfFockLeftCurrentTransport.targetSlice D hu b delta)
        (fun r => observation.readout () ⟨D,hu,neutralMode D i d a,gamma+1,b,delta,r⟩ ())
        (gamma+1)

theorem step_bridge : stepScope ↔ stepArena.Law actual := Iff.rfl
theorem step_positive : stepArena.Law actual := step_bridge.mp step_source

/- Faithful full-source reconstruction and actual-positive laws only.
A lawful enrolled-template readout, sourceSelection, whole-family variation,
sensitivity and observational dependence remain unproved. This attempt makes
no declared_validated or completed four-slot registration claim. -/
end Reg.D5.S3.VertexAlgebra.GroundRightCurrentTransport.FirstSourceClosure
