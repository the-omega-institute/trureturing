/- GID: D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity
   generality: G
   mirror-B: D5/B/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: With [P,T] defined as P*T - T*P, complementary elements Q = 1 - P in any possibly noncommutative ring satisfy [P,T] = P*T*Q - Q*T*P without idempotence or nondegeneracy assumptions, including P = 0, P = 1, empty matrices, and zero rings. -/

import D5.S3.Observer.HiddenFlow.InfinitesimalReducingCriterion

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'commutator_eq_cross_blocks' D5 Golden/Frozen/accepted`
     returned no public or private hit.
   * Repository searches for projection commutators and cross blocks found the public
     `commutes_visibleProjectionMatrix_iff_reducing` and
     `reducing_iff_cross_projection_blocks_eq_zero`, but no cross-block identity.
   * A separate search of private projection and commutator helpers found no statement
     of the identity; unrelated private projection lemmas were not reusable.
   * Pinned Mathlib searches found `mul_one_sub`, `one_sub_mul`, and
     `mul_one_sub_mul`, but no packaged theorem for this commutator identity.
   * The identity therefore uses basic ring distributivity, while the iff corollary
     directly composes the two public repository theorems above.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

open D5.S3.Observer.HiddenFlow.InfinitesimalReducingCriterion
open D5.S3.Observer.HiddenFlow.VisibleHiddenProjectionCriteria

/-- The commutator convention used here is `[P, T] = P * T - T * P`. -/
def commutator {A : Type*} [Ring A] (P T : A) : A :=
  P * T - T * P

/-- Splitting the identity as `P + Q` expresses the commutator as the difference of
the two directed cross blocks. Idempotence of `P` is not needed for this identity. -/
theorem commutator_eq_cross_blocks {A : Type*} [Ring A] (P Q T : A)
    (hQ : Q = 1 - P) :
    P * T - T * P = P * T * Q - Q * T * P := by
  have hComplement : P + Q = 1 := by
    rw [hQ]
    simp
  calc
    P * T - T * P = P * T * 1 - 1 * T * P := by simp
    _ = P * T * (P + Q) - (P + Q) * T * P := by rw [hComplement]
    _ = (P * T * P + P * T * Q) - (P * T * P + Q * T * P) := by
      simp only [mul_add, add_mul, mul_assoc]
    _ = P * T * Q - Q * T * P := by abel

/-- For the visible projection of a complementary decomposition, commutation is
equivalent to the vanishing of both directed cross blocks. -/
theorem visible_projection_commutes_iff_cross_blocks_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (V R : Submodule ℂ (n → ℂ)) (h : IsCompl V R) (T : Matrix n n ℂ) :
    visibleProjectionMatrix V R h * T = T * visibleProjectionMatrix V R h ↔
      visibleProjection V R h ∘ₗ Matrix.toLin' T ∘ₗ hiddenProjection V R h = 0 ∧
        hiddenProjection V R h ∘ₗ Matrix.toLin' T ∘ₗ visibleProjection V R h = 0 := by
  rw [eq_comm, commutes_visibleProjectionMatrix_iff_reducing,
    reducing_iff_cross_projection_blocks_eq_zero]

example :
    let P : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]
    let T : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 0, 0]
    commutator P T = P * T * (1 - P) - (1 - P) * T * P := by
  dsimp only
  exact commutator_eq_cross_blocks _ _ _ rfl

#print axioms commutator_eq_cross_blocks
#print axioms visible_projection_commutes_iff_cross_blocks_eq_zero

end D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
