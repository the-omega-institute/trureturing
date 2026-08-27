/- GID: D5/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence
   generality: G
   mirror-B: D5/B/S3/Observer/VisibleDescent/TargetObservabilityFourWayEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A linear target is observable exactly when its Riesz vector lies in the adjoint range. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint

/- Library-search audit trail (2026-08-28):
   * Repository searches for target observability, fiber constancy, kernel
     inclusion, Riesz vectors, and adjoint-range witnesses found no theorem
     exposing all four equivalent clauses and the reconstruction formula.
   * `FiniteObservabilityOrthogonalDuality` concerns a finite Krylov-space
     kernel rather than a single target functional, so it is not an exact hit.
   * Exact pinned-Mathlib component hits `LinearMap.orthogonal_ker` and
     `LinearMap.adjoint_inner_left` supply the finite-dimensional duality and
     reconstruction steps. No full-statement Mathlib hit was found. -/

open scoped InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.VisibleDescent.TargetObservabilityFourWayEquivalence

/-- Fiber determination, kernel inclusion, adjoint-range membership, and an
adjoint preimage are equivalent descriptions of a linearly observable target.
Every adjoint preimage gives the stated observation-space reconstruction. -/
theorem target_observability_four_way_equivalence
    {K X Y : Type*} [RCLike K]
    [NormedAddCommGroup X] [InnerProductSpace K X]
    [FiniteDimensional K X]
    [NormedAddCommGroup Y] [InnerProductSpace K Y]
    [FiniteDimensional K Y]
    (M : X →ₗ[K] Y) (t : X →ₗ[K] K) (v_t : X)
    (riesz : forall x, t x = ⟪v_t, x⟫_K) :
    ((forall x y, M x = M y -> t x = t y) <->
        LinearMap.ker M <= LinearMap.ker t) /\
      ((forall x y, M x = M y -> t x = t y) <->
        v_t ∈ LinearMap.range M.adjoint) /\
      ((forall x y, M x = M y -> t x = t y) <->
        exists a : Y, M.adjoint a = v_t) /\
      (forall a : Y, M.adjoint a = v_t ->
        forall x : X, t x = ⟪a, M x⟫_K) := by
  have fiber_iff_kernel :
      (forall x y, M x = M y -> t x = t y) <->
        LinearMap.ker M <= LinearMap.ker t := by
    constructor
    · intro determined z hz
      rw [LinearMap.mem_ker] at hz ⊢
      have sameTarget := determined z 0 (by simpa using hz)
      simpa using sameTarget
    · intro kernelInclusion x y sameObservation
      apply sub_eq_zero.mp
      have differenceInKernel : x - y ∈ LinearMap.ker M := by
        rw [LinearMap.mem_ker]
        simp [sameObservation]
      have targetDifferenceZero :=
        LinearMap.mem_ker.mp (kernelInclusion differenceInKernel)
      simpa using targetDifferenceZero
  have fiber_iff_range :
      (forall x y, M x = M y -> t x = t y) <->
        v_t ∈ LinearMap.range M.adjoint := by
    constructor
    · intro determined
      have kernelInclusion := fiber_iff_kernel.mp determined
      have orthogonalKernel : v_t ∈ (LinearMap.ker M)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro z hz
        rw [← riesz z]
        exact LinearMap.mem_ker.mp (kernelInclusion hz)
      rwa [LinearMap.orthogonal_ker] at orthogonalKernel
    · rintro ⟨a, ha⟩ x y sameObservation
      rw [riesz x, riesz y, ← ha]
      simpa only [LinearMap.adjoint_inner_left] using
        congrArg (fun observed => ⟪a, observed⟫_K) sameObservation
  have fiber_iff_witness :
      (forall x y, M x = M y -> t x = t y) <->
        exists a : Y, M.adjoint a = v_t := by
    exact fiber_iff_range
  refine ⟨fiber_iff_kernel, fiber_iff_range, fiber_iff_witness, ?_⟩
  intro a ha x
  rw [riesz x, ← ha, LinearMap.adjoint_inner_left]

example : Real := 0

example : forall x : Real,
    (LinearMap.id : Real →ₗ[Real] Real) x = ⟪(1 : Real), x⟫_Real := by
  simp

#print axioms target_observability_four_way_equivalence

end D5.S3.Observer.VisibleDescent.TargetObservabilityFourWayEquivalence
