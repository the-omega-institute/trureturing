/- GID: D5/S3/ConceptDynamics/RefinementFactorization/CompatiblePrecisionTowerMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/RefinementFactorization/CompatiblePrecisionTowerMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible precision layers refine monotonically and shrink equality kernels. -/

import D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
import D5.S3.ConceptDynamics.ConceptJoinUniversal
import Mathlib.Data.Nat.Prime.Basic

/- Library-search audit trail (2026-08-25):
   * Exact family hit `ConceptJoinUniversal.Refines` is the canonical readout
     factorization predicate and is used directly in the public statement.
   * Exact repository hit `relative_identity_refinement` proves equality-kernel
     antitonicity from the same adjacent compatibility equation; its first
     public conjunct is applied below.
   * `IndexedReadoutMonotonicity` concerns restriction along finite coordinate
     sets, not adjacent layers of one compatible precision tower.
   * Pinned Mathlib searches found `Function.FactorsThrough` and specialized
     linear kernel-composition lemmas, but no theorem packaging both clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.RefinementFactorization.CompatiblePrecisionTowerMonotonicity

open D5.S0.Rewriting.Quotients.RelativeIdentityRefinement
open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u v

/-- A compatibility map from precision `k + 1` to precision `k` witnesses
readout refinement, so equality at the finer level implies equality at the
coarser level. -/
theorem compatible_precision_tower_monotonicity
    {X : Type u}
    (O : {p : Nat // Nat.Prime p} -> Nat -> Type v)
    (q : (p : {p : Nat // Nat.Prime p}) -> (k : Nat) -> X -> O p k)
    (lower : (p : {p : Nat // Nat.Prime p}) -> (k : Nat) ->
      O p (k + 1) -> O p k)
    (compatible : forall p k, q p k = lower p k ∘ q p (k + 1))
    (p : {p : Nat // Nat.Prime p}) (k : Nat) :
    Refines (q p k) (q p (k + 1)) ∧
      Setoid.ker (q p (k + 1)) <= Setoid.ker (q p k) := by
  constructor
  · exact ⟨lower p k, compatible p k⟩
  · exact
      (relative_identity_refinement
        (q p (k + 1)) (q p k) (lower p k) (compatible p k)).1

example : {p : Nat // Nat.Prime p} := ⟨2, Nat.prime_two⟩

example :
    let O : {p : Nat // Nat.Prime p} -> Nat -> Type := fun _ _ => Bool
    let q : (p : {p : Nat // Nat.Prime p}) -> (k : Nat) -> Bool -> O p k :=
      fun _ _ x => x
    let lower : (p : {p : Nat // Nat.Prime p}) -> (k : Nat) ->
        O p (k + 1) -> O p k := fun _ _ x => x
    forall p k, q p k = lower p k ∘ q p (k + 1) := by
  dsimp
  intro _ _
  funext x
  rfl

#print axioms compatible_precision_tower_monotonicity

end D5.S3.ConceptDynamics.RefinementFactorization.CompatiblePrecisionTowerMonotonicity
