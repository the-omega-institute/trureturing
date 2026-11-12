/-
Source-only implementation.  Native elaboration and kernel acceptance are pending.
This module records the full algebraic-dual compatibility of the supplied
original twist.  The transpose is complex-linear; no conjugation or inverse of
its scalar occurs.  The original quadratic representative/carry data stay in
the consumed suppliers.
-/
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBiduality
import D5.S3.VertexAlgebra.Modules.ActualWeakModuleBalancing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct DirectSum VertexOperator

namespace D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonDuality

open LatticeGeneratingFieldLocality LatticeDiscriminantTheta
open LatticeDualCosetModule LatticeDualCosetTransport LatticeChargedTransport
open ActualWeakModuleSectorCoordinates ActualWeakModuleClassification
open ActualWeakModuleHom ActualWeakModuleRealization ActualWeakModuleDuality
open ActualWeakModuleBalancing
open FullJacobiCurrentTransport FullJacobiIntertwiner

universe u v
variable {D : LatticeData}
attribute [local instance] Classical.propDecidable

section Scalar
variable (hD : (gramReal D).PosDef)

/-- The quadratic phase is even, using the supplied k-smul clause at k = -1. -/
include hD in
theorem thetaScalar_neg (c : Discriminant D) :
    thetaScalar (-c) = thetaScalar c := by
  unfold thetaScalar
  rw [show quadraticClass D (-c) = quadraticClass D c by
    simpa using (discriminant_quadratic D hD).2.1 c (-1 : ℤ)]

end Scalar

section Original
variable {X : Type u} [AddCommGroup X] [Module ℂ X]
variable (A : FullJacobiLatticeModule D X)
variable (hD : (gramReal D).PosDef)

private theorem dual_theta_restrict (c : Discriminant D)
    (z : Multiplicity (dualModule A) c) :
    restrict (dualHom hD (theta A hD).hom) c z =
      thetaScalar (-c) • z := by
  let e := multiplicityEquiv (DualMultiplicity A) hD c
  have hz : z = iota (DualMultiplicity A) c (e z) := by
    symm
    simpa [e, dualModule, DualMultiplicity, multiplicityEquiv] using
      (e.symm_apply_apply z)
  apply e.injective
  apply LinearMap.ext
  intro y
  rw [hz, dualHom_restrict]
  simp only [e, LinearMap.comp_apply, map_smul, kappa_iota]
  rw [restrict_theta]
  simp only [map_smul, smul_eq_mul] <;> ring

theorem theta_dual_compatibility :
    dualHom hD (theta A hD).hom = (theta (dualModule A) hD).hom := by
  apply (recordEquiv (dualModule A) (dualModule A)).injective
  apply (homMultiplicityEquiv (dualModule A) (dualModule A) hD).injective
  funext c
  apply LinearMap.ext
  intro z
  rw [dual_theta_restrict, restrict_theta, thetaScalar_neg hD]

end Original
end D5.S3.VertexAlgebra.Modules.ActualWeakModuleRibbonDuality
