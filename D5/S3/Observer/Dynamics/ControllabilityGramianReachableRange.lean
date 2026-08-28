/- GID: D5/S3/Observer/Dynamics/ControllabilityGramianReachableRange
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/ControllabilityGramianReachableRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The stable controllability Gramian has exactly the reachable range. -/

import D5.S3.Observer.LinearMemory.ObservabilityGramianKernelEnergy
import D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
import D5.S3.ObserverMemory.Dynamics.InfiniteObservabilityOrthogonalDuality

/- Library-search audit trail (2026-08-28):
   * D5 body-shape and name searches found no controllability-Gramian
     construction. The canonical `discountedObservabilityGramian` is reused
     under the adjoint substitution at weight one, which unfolds to the
     source's controllability series.
   * The canonical D5 `reachableSubspace` is imported rather than redeclared.
     Its body is the span of all iterated input directions.
   * `observability_gramian_kernel_energy` and
     `infinite_unobservable_eq_observable_orthogonal` supply the dual kernel
     bridge. Pinned Mathlib's adjoint-range and double-orthogonal identities
     then give the exact range equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Dynamics.ControllabilityGramianReachableRange

open InnerProductSpace RCLike
open scoped InnerProduct ComplexConjugate ComplexOrder

open D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity
open D5.S3.Observer.LinearMemory.ObservabilityGramianKernelEnergy
open D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
open D5.S3.ObserverMemory.Dynamics.InfiniteObservabilityOrthogonalDuality

/-- The ordinary controllability Gramian, constructed as the weight-one
observability Gramian of the adjoint system. Its terms are
`A^k B B† (A†)^k`. -/
noncomputable def controllabilityGramian
    {K V U : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup U] [InnerProductSpace K U]
    [FiniteDimensional K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) : V →L[K] V :=
  discountedObservabilityGramian A.adjoint B.adjoint 1

/-- If the exact ordinary controllability-Gramian series is summable, its
linear range equals the canonical span of all iterated input directions. -/
theorem controllability_gramian_range_eq_reachable
    {K V U : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V]
    [NormedAddCommGroup U] [InnerProductSpace K U]
    [FiniteDimensional K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V)
    (stable : Summable (discountedGramianTerm A.adjoint B.adjoint 1)) :
    LinearMap.range (controllabilityGramian A B).toLinearMap =
      reachableSubspace A B := by
  letI := FiniteDimensional.complete K V
  letI := FiniteDimensional.complete K U
  have gramianSelfAdjoint : IsSelfAdjoint (controllabilityGramian A B) := by
    rw [isSelfAdjoint_iff]
    change star (∑' n : Nat,
      discountedGramianTerm A.adjoint B.adjoint 1 n) =
        ∑' n : Nat, discountedGramianTerm A.adjoint B.adjoint 1 n
    rw [tsum_star]
    congr 1
    funext n
    exact ((ContinuousLinearMap.isPositive_adjoint_comp_self
      (observedIterate A.adjoint B.adjoint n)).smul_of_nonneg
        (RCLike.ofReal_nonneg.mpr
          (pow_nonneg (by positivity : (0 : Real) ≤ 1) n))).isSelfAdjoint.star_eq
  have gramianSymmetric :
      (controllabilityGramian A B).toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).2
      ((controllabilityGramian A B).isSelfAdjoint_toLinearMap_iff.2
        gramianSelfAdjoint)
  have kernelEq :
      LinearMap.ker (controllabilityGramian A B).toLinearMap =
        (reachableSubspace A B)ᗮ := by
    calc
      LinearMap.ker (controllabilityGramian A B).toLinearMap =
          ⨅ k : Nat,
            LinearMap.ker (B.adjoint.comp (A.adjoint ^ k)) :=
        (observability_gramian_kernel_energy A.adjoint B.adjoint stable).1
      _ = (Submodule.span K
          {v | ∃ k : Nat, ∃ u : U,
            v = ((A.adjoint).adjoint ^ k) ((B.adjoint).adjoint u)})ᗮ :=
        infinite_unobservable_eq_observable_orthogonal
          A.adjoint B.adjoint
      _ = (reachableSubspace A B)ᗮ := by
        simp only [LinearMap.adjoint_adjoint]
        rfl
  calc
    LinearMap.range (controllabilityGramian A B).toLinearMap =
        (LinearMap.ker (controllabilityGramian A B).toLinearMap)ᗮ := by
      rw [LinearMap.orthogonal_ker, gramianSymmetric.adjoint_eq]
    _ = ((reachableSubspace A B)ᗮ)ᗮ := by rw [kernelEq]
    _ = reachableSubspace A B := Submodule.orthogonal_orthogonal _

#print axioms controllability_gramian_range_eq_reachable

end D5.S3.Observer.Dynamics.ControllabilityGramianReachableRange
