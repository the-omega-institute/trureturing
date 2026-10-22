import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.ChargedResidue.CollisionTransform

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.VertexAlgebra.ChargedResidue.CollisionTransform
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockChargedResidue
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators TensorProduct

abbrev sourceScope := type_of% (@chargedPhysicalCollisionRow_transform_native)
theorem source_actual : sourceScope := @chargedPhysicalCollisionRow_transform_native

abbrev Parameters := Σ data : {D : LatticeData // IsUnit D.G.det},
  Charge data.val × Charge data.val × Bool × Bool × ℤ × ℤ × ℤ × ℤ × ℕ × ℕ

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => ActualTensor p.1.val p.1.property)
  (fun p => ActualTensor p.1.val p.1.property)

def actual : Realization signature := realize signature (fun _ p x =>
  let D := p.1.val
  let hu := p.1.property
  let sigma := p.2.1
  let tau := p.2.2.1
  let epsilon := p.2.2.2.1
  let eta := p.2.2.2.2.1
  let gamma := p.2.2.2.2.2.1
  let delta := p.2.2.2.2.2.2.1
  let r := p.2.2.2.2.2.2.2.1
  let n := p.2.2.2.2.2.2.2.2.1
  let l := p.2.2.2.2.2.2.2.2.2.1
  let K := p.2.2.2.2.2.2.2.2.2.2
  ∑ k ∈ Finset.range (((K : ℤ) - r).toNat - l), Ring.choose ((gamma : ℂ) / 2) k •
    chargedPhysicalCollisionRow D hu sigma tau epsilon eta gamma delta r n (l + k) x)
  (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law observation := ∀ (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (epsilon eta : Bool) (gamma delta r n : ℤ) (l K : ℕ),
    (bilinear D sigma tau).natAbs ≤ K → ∀ (p : Oscillator D) (g : ActualGround D hu),
    observation.readout () ⟨⟨D, hu⟩, sigma, tau, epsilon, eta, gamma, delta, r, n, l, K⟩
        (p ⊗ₜ[ℂ] g) =
      (1 / 4 : ℂ) • (transformedCollisionKernel D hu sigma tau gamma delta r n l p g +
        projectedSign eta • transformedCollisionKernel D hu sigma (-tau) gamma delta r n l p g +
        projectedSign epsilon • transformedCollisionKernel D hu (-sigma) tau gamma delta r n l p g +
        (projectedSign epsilon * projectedSign eta) •
          transformedCollisionKernel D hu (-sigma) (-tau) gamma delta r n l p g)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl
theorem actual_positive : arena.Law actual := source_bridge.mp source_actual

/- Exact source reconstruction and actual-positive evidence retain the full
   family. Whole-family variation, sensitivity, observational dependence and
   structural sourceSelection are additional unfinished Registration targets. -/
end Reg.D5.S3.VertexAlgebra.ChargedResidue.CollisionTransform
