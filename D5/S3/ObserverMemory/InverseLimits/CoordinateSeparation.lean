/- GID: D5/S3/ObserverMemory/InverseLimits/CoordinateSeparation
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/CoordinateSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint coordinates separate points exactly when their common kernels are trivial. -/

import Mathlib.Data.Setoid.Basic
import Mathlib.LinearAlgebra.Pi

/- Library-search audit trail (2026-08-18):
   * Pinned Mathlib supplies `Setoid.injective_iff_ker_bot`, `LinearMap.ker_pi`, and
     `LinearMap.ker_eq_bot_of_injective`; all three are applied below.
   * Local D5 searches found the equality-kernel identity for a joint observation, but no theorem
     combining point separation with the linear common-kernel criterion.
   * Loogle returned exact hits for the Setoid and indexed-kernel identities. Local source search
     found the injective linear-map helper. LeanSearch's `/api/search` endpoint returned HTTP 404
     and therefore supplied no search conclusion. -/

namespace D5.S3.ObserverMemory.InverseLimits.CoordinateSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w x

/-- A family of linear coordinates separates points exactly when both its equivalence-relation
kernel and its linear kernel are trivial. The bottom setoid is the diagonal equality relation. -/
theorem coordinate_separation_criterion
    {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    {I : Type w} {N : I -> Type x}
    [(i : I) -> AddCommMonoid (N i)] [(i : I) -> Module R (N i)]
    (q : (i : I) -> M →ₗ[R] N i) :
    Function.Injective (LinearMap.pi q) ↔
      (⨅ i, Setoid.ker (q i)) = ⊥ ∧
        (⨅ i, LinearMap.ker (q i)) = ⊥ := by
  have hSetoidKernel :
      Setoid.ker (LinearMap.pi q) = ⨅ i, Setoid.ker (q i) := by
    apply le_antisymm
    · refine le_iInf fun i => ?_
      intro a b hab
      exact congrFun hab i
    · intro a b hab
      funext i
      exact (iInf_le (fun j => Setoid.ker (q j)) i) hab
  constructor
  · intro hInjective
    have hSetoid : Setoid.ker (LinearMap.pi q) = ⊥ :=
      (Setoid.injective_iff_ker_bot (LinearMap.pi q)).mp hInjective
    have hLinear : LinearMap.ker (LinearMap.pi q) = ⊥ :=
      LinearMap.ker_eq_bot_of_injective hInjective
    rw [hSetoidKernel] at hSetoid
    rw [LinearMap.ker_pi] at hLinear
    exact ⟨hSetoid, hLinear⟩
  · rintro ⟨hSetoid, _⟩
    apply (Setoid.injective_iff_ker_bot (LinearMap.pi q)).mpr
    rwa [hSetoidKernel]

#print axioms coordinate_separation_criterion

end D5.S3.ObserverMemory.InverseLimits.CoordinateSeparation
