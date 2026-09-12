# Integer Affine Square Collision

## Abstract

Integer affine maps with fewer rows than columns identify positive natural inputs with unequal square sums.

**Theorem 1.1 (A positive natural collision with unequal square sums).**

Lean statement: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural dimensions with fewer rows than columns, the integer affine map has two strictly positive natural inputs with equal affine images and unequal natural square sums. The fiber is found by the theorem; no prescribed fiber is assumed.

The construction is the strict-positive clause of CONTEXTUAL_SPACETIME_ARITHMETIC §45.1, Lemma 7 (FIBER-SQUARE-ESCAPE), corresponding to intake M11. A nonzero integer kernel vector d gives the positive triple z = abs(d) + 1, z+d and z-d. Both absolute-value bounds prove every coordinate is at least one, including zero coordinates of d. The second square difference is twice the positive square sum of d, so either the plus or the minus neighbor separates from z. Selection occurs after the shift.

Mathlib supplies LinearMap.finrank_le_finrank_of_injective over StrongRankCondition Int, Module.finrank_fin_fun, LinearMap.ker_eq_bot, Submodule.exists_mem_ne_zero_of_ne_bot and Finset.sum_mul_self_eq_zero_iff. The instance is supplied by Mathlib.LinearAlgebra.FreeModule.StrongRankCondition. This reuses integral rank theory in place of the source rational rank-nullity and denominator-clearing step.

Each selected integer coordinate is nonnegative before Int.toNat is used. Coordinate cast-back equalities give positive natural coordinates, whole-function affine transport and cast equality for both sums of squares. Equality of the natural sums would contradict the integer separation.

Source coordinates 1,...,s correspond to Fin s by j ↦ j.val+1, consistently for columns, vectors and sums. The source ordinary clause follows by forgetting positivity. The exact general derivations below also retain arbitrary A and b for the zero-row case, and every m for the one-extra-column case used by P68. They are anonymous validations, not additional declarations or Describe anchors.

This general arithmetic theorem has utility kind none. It proves no history realization, P68 contextual separation, ZFC interpretation, representation-domain claim or conservativity result.

L7.strictly_positive: `example : ∀ (m s : ℕ), m < s → ∀ (A : Matrix (Fin m) (Fin s) ℤ) (b : Fin m → ℤ), ∃ u v : Fin s → ℕ, (∀ j, 0 < u j) ∧ (∀ j, 0 < v j) ∧ (A.mulVec (fun j => (u j : ℤ)) + b = A.mulVec (fun j => (v j : ℤ)) + b) ∧ ((∑ j, u j ^ 2) ≠ (∑ j, v j ^ 2)) := IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne`

L7.ordinary: `example : ∀ (m s : ℕ), m < s → ∀ (A : Matrix (Fin m) (Fin s) ℤ) (b : Fin m → ℤ), ∃ u v : Fin s → ℕ, (A.mulVec (fun j => (u j : ℤ)) + b = A.mulVec (fun j => (v j : ℤ)) + b) ∧ ((∑ j, u j ^ 2) ≠ (∑ j, v j ^ 2)) := fun m s h A b => Exists.elim (IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne m s h A b) (fun u hu => Exists.elim hu (fun v hv => ⟨u, v, hv.2.2.1, hv.2.2.2⟩))`

L7.m_zero_positive: `example : ∀ (s : ℕ), 0 < s → ∀ (A : Matrix (Fin 0) (Fin s) ℤ) (b : Fin 0 → ℤ), ∃ u v : Fin s → ℕ, (∀ j, 0 < u j) ∧ (∀ j, 0 < v j) ∧ (A.mulVec (fun j => (u j : ℤ)) + b = A.mulVec (fun j => (v j : ℤ)) + b) ∧ ((∑ j, u j ^ 2) ≠ (∑ j, v j ^ 2)) := fun s hs A b => IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne 0 s hs A b`

L7.m_zero_ordinary: `example : ∀ (s : ℕ), 0 < s → ∀ (A : Matrix (Fin 0) (Fin s) ℤ) (b : Fin 0 → ℤ), ∃ u v : Fin s → ℕ, (A.mulVec (fun j => (u j : ℤ)) + b = A.mulVec (fun j => (v j : ℤ)) + b) ∧ ((∑ j, u j ^ 2) ≠ (∑ j, v j ^ 2)) := fun s hs A b => Exists.elim (IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne 0 s hs A b) (fun u hu => Exists.elim hu (fun v hv => ⟨u, v, hv.2.2.1, hv.2.2.2⟩))`

P68.L7_s_m_plus_one: `example : ∀ (m : ℕ), ∀ (A : Matrix (Fin m) (Fin (m+1)) ℤ) (b : Fin m → ℤ), ∃ u v : Fin (m+1) → ℕ, (∀ j, 0 < u j) ∧ (∀ j, 0 < v j) ∧ (A.mulVec (fun j => (u j : ℤ)) + b = A.mulVec (fun j => (v j : ℤ)) + b) ∧ ((∑ j, u j ^ 2) ≠ (∑ j, v j ^ 2)) := fun m A b => IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne m (m+1) (Nat.lt_succ_self m) A b`

## References

- Truth anchor: `D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerAffineSquareCollision.exists_pos_nat_affine_fiber_sq_ne`
