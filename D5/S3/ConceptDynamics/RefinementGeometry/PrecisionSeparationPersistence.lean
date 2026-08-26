/- GID: D5/S3/ConceptDynamics/RefinementGeometry/PrecisionSeparationPersistence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementGeometry/PrecisionSeparationPersistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separation at one compatible precision layer persists at every finer layer. -/

import D5.S3.ConceptDynamics.RefinementFactorization.CompatiblePrecisionTowerMonotonicity

/- Library-search audit trail (2026-08-26):
   * Exact repository searches for precision persistence, higher-layer
     separation, and antitone equality kernels found no theorem covering all
     later layers.
   * The frozen `compatible_precision_tower_monotonicity` is the closest D5
     hit. It proves the adjacent refinement and equality-kernel inclusion
     cited immediately before source theorem 7.1; the proof below applies its
     kernel clause inductively.
   * `IndexedReadoutMonotonicity` concerns restriction of one coordinate
     family, while `RefinementShrinksIndistinguishability` covers one given
     refinement step. Neither quantifies over a compatible precision tower.
   * Pinned Mathlib searches found generic induction and function-composition
     infrastructure but no theorem for this source-specific dependent tower. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementGeometry.PrecisionSeparationPersistence

open D5.S3.ConceptDynamics.RefinementFactorization.CompatiblePrecisionTowerMonotonicity

universe u v

/-- If two states are separated by layer `k` of a compatible precision tower,
then every layer `m >= k` still separates them. -/
theorem precision_separation_persists
    {X : Type u}
    (O : Nat -> Type v)
    (q : (k : Nat) -> X -> O k)
    (lower : (k : Nat) -> O (k + 1) -> O k)
    (compatible : forall k, q k = lower k ∘ q (k + 1))
    {k m : Nat} (x y : X)
    (higher : k ≤ m)
    (separated : q k x ≠ q k y) :
    q m x ≠ q m y := by
  induction m, higher using Nat.le_induction with
  | base => exact separated
  | @succ m higher persists =>
      intro sameAtNext
      apply persists
      exact
        (compatible_precision_tower_monotonicity
          (O := fun _ level => O level)
          (q := fun _ level => q level)
          (lower := fun _ level => lower level)
          (compatible := fun _ level => compatible level)
          (p := (by exact ⟨2, Nat.prime_two⟩))
          (k := m)).2 sameAtNext

#print axioms precision_separation_persists

end D5.S3.ConceptDynamics.RefinementGeometry.PrecisionSeparationPersistence
