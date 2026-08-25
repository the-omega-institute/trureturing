/- GID: D5/S3/ConceptDynamics/Attribution/SymmetricResponsibilityAllocation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/SymmetricResponsibilityAllocation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A normalized equivariant allocation is uniform at a fully symmetric event. -/

import D5.S3.ConceptDynamics.Attribution.SymmetricEventNoUniqueCulprit
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-25):
   * Repository searches for symmetric responsibility, uniform weights, permutation-fixed
     vectors, and the atom fingerprint found no exact theorem.
   * The adjacent frozen module supplies `IsCompletelySymmetric`; it treats a selected
     culprit rather than a real-valued normalized allocation.
   * Pinned Mathlib has no exact uniform-allocation theorem. The proof directly reuses
     `Equiv.swap_apply_left`, finite-sum simplification, and `Fintype.card_fin`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.SymmetricResponsibilityAllocation

open scoped BigOperators
open D5.S3.ConceptDynamics.Attribution.SymmetricEventNoUniqueCulprit

/-- At a fully permutation-symmetric event, equivariance first makes the allocation
permutation-invariant; normalization then forces every responsibility coordinate to be `1 / n`.
Nonnegativity and normalization are stated on the source allocation rather than built into it. -/
theorem symmetric_responsibility_is_uniform
    {n : Nat} {Event : Type*}
    (act : Equiv.Perm (Fin n) -> Event -> Event)
    (allocation : Event -> Fin n -> Real) (event : Event)
    (_nonnegative : forall i, 0 <= allocation event i)
    (normalized : (∑ i, allocation event i) = 1)
    (equivariant : forall sigma current i,
      allocation (act sigma current) (sigma i) = allocation current i)
    (symmetric : IsCompletelySymmetric act event) :
    (forall (sigma : Equiv.Perm (Fin n)) (i : Fin n),
      allocation event (sigma i) = allocation event i) ∧
      (forall i, allocation event i = 1 / (n : Real)) := by
  have invariant : forall (sigma : Equiv.Perm (Fin n)) (i : Fin n),
      allocation event (sigma i) = allocation event i := by
    intro sigma i
    calc
      allocation event (sigma i) = allocation (act sigma event) (sigma i) := by
        rw [symmetric sigma]
      _ = allocation event i := equivariant sigma event i
  refine ⟨invariant, ?_⟩
  intro i
  have constant : forall j, allocation event j = allocation event i := by
    intro j
    simpa only [Equiv.swap_apply_left] using invariant (Equiv.swap i j) i
  have constantSum : (∑ _j : Fin n, allocation event i) = 1 := by
    calc
      (∑ _j : Fin n, allocation event i) = ∑ j, allocation event j := by
        exact Finset.sum_congr rfl fun j _ => (constant j).symm
      _ = 1 := normalized
  have n_ne_zero : (n : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at constantSum
  apply (eq_div_iff n_ne_zero).2
  simpa only [mul_comm] using constantSum

#print axioms symmetric_responsibility_is_uniform

end D5.S3.ConceptDynamics.Attribution.SymmetricResponsibilityAllocation
