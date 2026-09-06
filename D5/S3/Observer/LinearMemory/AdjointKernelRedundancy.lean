/- GID: D5/S3/Observer/LinearMemory/AdjointKernelRedundancy
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/AdjointKernelRedundancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The adjoint kernel is exactly the space of redundant protocol coefficients. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Pi

/- Library-search audit trail (2026-09-05):
   * Repository searches for adjoint kernels, protocol linear combinations,
     synthesis maps, and redundant coefficient directions found no equivalent
     theorem. `DualGramKernels` identifies Gram kernels but does not calculate
     the adjoint as the linear combination of protocol representatives.
   * Blueprint, digest, exact-module, generalized kernel/range, and all refreshed
     in-flight branch searches found no equivalent declaration or module.
   * Pinned Mathlib supplies `LinearMap.adjoint_inner_left`, `PiLp.inner_apply`,
     and the finite-sum inner-product identities. It has no declaration packaging
     this coordinate analysis map with its explicit synthesis formula.
   * Escape witness: the proof calculates the adjoint of the constructed finite
     protocol analysis map by testing every inner product and reducing both sides
     to the same indexed sum. There are no direct frozen prerequisites. -/

namespace D5.S3.Observer.LinearMemory.AdjointKernelRedundancy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For a finite family of real Hilbert-space protocol representatives, the
kernel of the adjoint analysis map consists exactly of coefficient vectors whose
linear combination of representatives vanishes. -/
theorem adjoint_kernel_redundancy
    {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι]
    (ell : ι → V) (a : EuclideanSpace ℝ ι) :
    let observation : V →ₗ[ℝ] EuclideanSpace ℝ ι :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp
        (LinearMap.pi fun i => (innerSL ℝ (ell i)).toLinearMap)
    a ∈ observation.adjoint.ker ↔
      ∑ i : ι, (a i) • ell i = 0 := by
  dsimp only
  rw [LinearMap.mem_ker]
  have hAdjoint :
      (LinearMap.adjoint
        ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toLinearMap.comp
          (LinearMap.pi fun i => (innerSL ℝ (ell i)).toLinearMap))) a =
        ∑ i : ι, (a i) • ell i := by
    apply ext_inner_right ℝ
    intro x
    rw [LinearMap.adjoint_inner_left]
    simp [PiLp.inner_apply, sum_inner, real_inner_smul_left,
      LinearMap.comp_apply, mul_comm]
  rw [hAdjoint]

#print axioms adjoint_kernel_redundancy

end D5.S3.Observer.LinearMemory.AdjointKernelRedundancy
