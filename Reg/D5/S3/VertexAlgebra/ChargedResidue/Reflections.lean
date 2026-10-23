import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.Reflections

set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.Reflections
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients LatticeHalfFockChargedResidue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct

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
  n : ℤ
  l : ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => Oscillator p.D × ActualGround p.D p.hu) (fun p => ActualTensor p.D p.hu)

def doubleActual : Realization signature := realize signature (fun _ p x =>
  transformedCollisionKernel p.D p.hu (-p.sigma) (-p.tau) p.gamma p.delta p.r p.n p.l x.1 x.2)
  (fun empty => nomatch empty)

abbrev doubleScope := type_of% (@transformedCollisionKernel_double_reflection)
theorem double_source : doubleScope := @transformedCollisionKernel_double_reflection

def doubleArena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (gamma delta r n : ℤ) (l : ℕ) (p : Oscillator D) (g : ActualGround D hu),
    observation.readout () ⟨D,hu,sigma,tau,false,false,gamma,delta,r,n,l⟩ (p,g) =
      (-1 : ℂ)^(gamma+delta) • transformedCollisionKernel D hu sigma tau gamma delta r n l p g

theorem double_bridge : doubleScope ↔ doubleArena.Law doubleActual := Iff.rfl
theorem double_positive : doubleArena.Law doubleActual := double_bridge.mp double_source

def actual : Realization signature := realize signature (fun _ p x =>
  (1/4 : ℂ) • (transformedCollisionKernel p.D p.hu p.sigma p.tau p.gamma p.delta p.r p.n p.l x.1 x.2 +
    projectedSign p.eta • transformedCollisionKernel p.D p.hu p.sigma (-p.tau) p.gamma p.delta p.r p.n p.l x.1 x.2 +
    projectedSign p.epsilon • transformedCollisionKernel p.D p.hu (-p.sigma) p.tau p.gamma p.delta p.r p.n p.l x.1 x.2 +
    (projectedSign p.epsilon * projectedSign p.eta) •
      transformedCollisionKernel p.D p.hu (-p.sigma) (-p.tau) p.gamma p.delta p.r p.n p.l x.1 x.2))
  (fun empty => nomatch empty)

abbrev sourceScope := type_of% (@charged_reflected_collision_diagonal)
theorem source_actual : sourceScope := @charged_reflected_collision_diagonal

def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ),
    (-1 : ℂ)^gamma = projectedSign epsilon → (-1 : ℂ)^delta = projectedSign eta →
    ∀ (l : ℕ) (p : Oscillator D) (g : ActualGround D hu),
    observation.readout () ⟨D,hu,sigma,tau,epsilon,eta,gamma,delta,r,n,l⟩ (p,g) =
      (chargeScalar D sigma * chargeScalar D tau) •
        ((∑ d ∈ (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).support,
          (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).coeff d *
            physicalResidueCollisionDiagonal D sigma tau gamma delta (r+l) (n-l) d)
          ⊗ₜ[ℂ] groundAction D hu sigma (groundAction D hu tau g))

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp source_actual

/- Every original input remains in these dependent families. A complete
   Registration still requires lawful enrolled-template readout, variation,
   sensitivity, observational dependence and structural sourceSelection. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.Reflections
