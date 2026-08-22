/- GID: D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning/UnreadStateOrthogonalProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unread measurement projects orthogonally onto block-diagonal matrices. -/

/- Library-search audit trail (2026-08-22):
   * `D5.S3.Observer.Conditioning` provides the exact complete projection-family predicate,
     unread channel, idempotence theorem, and fixed-point characterization; all four are reused.
   * `D5.S3.Quantum.Tomography.RankOneContextCommutator.hilbertSchmidtSquare` is the existing
     generic trace definition of squared Hilbert--Schmidt norm and is imported rather than copied.
   * Pinned-Mathlib exact hits `Matrix.trace_mul_comm`, `Matrix.trace_mul_cycle`,
     `Matrix.trace_sum`, and `Matrix.trace_conjTranspose` support the generic matrix proof.
   * Repository and pinned-Mathlib searches found no theorem packaging every clause for an
     arbitrary finite complete family of pairwise orthogonal projections. -/

import D5.S3.Observer.Conditioning
import D5.S3.Quantum.Tomography.RankOneContextCommutator

namespace D5.S3.Observer.Conditioning.UnreadStateOrthogonalProjection

open scoped BigOperators
open Matrix
open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Tomography.RankOneContextCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa] [DecidableEq kappa]
    {P : kappa -> Matrix n n ℂ}

omit [DecidableEq n] in
private theorem trace_compressed_mul (A B Q : Matrix n n ℂ) :
    Matrix.trace ((Q * A * Q) * B) = Matrix.trace (A * (Q * B * Q)) := by
  calc
    Matrix.trace ((Q * A * Q) * B) = Matrix.trace (Q * A * (Q * B)) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Q * B) * Q * A) := Matrix.trace_mul_cycle Q A (Q * B)
    _ = Matrix.trace (A * ((Q * B) * Q)) := Matrix.trace_mul_comm ((Q * B) * Q) A
    _ = Matrix.trace (A * (Q * B * Q)) := by rfl

omit [DecidableEq kappa] in
private theorem unreadState_conjTranspose (hP : IsRecordMeasurement P)
    (X : Matrix n n ℂ) :
    (unreadState P X)ᴴ = unreadState P Xᴴ := by
  classical
  rw [unreadState, Matrix.conjTranspose_sum, unreadState]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (P k)ᴴ = P k := by
    simpa only [Matrix.star_eq_conjTranspose] using hP.selfAdjoint k
  simp only [Matrix.conjTranspose_mul, hk, Matrix.mul_assoc]

omit [DecidableEq kappa] in
private theorem unreadState_hilbert_schmidt_self_adjoint
    (hP : IsRecordMeasurement P) (X Y : Matrix n n ℂ) :
    Matrix.trace ((unreadState P X)ᴴ * Y) =
      Matrix.trace (Xᴴ * unreadState P Y) := by
  classical
  rw [unreadState_conjTranspose hP X, unreadState, Matrix.sum_mul,
    Matrix.trace_sum, unreadState, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact trace_compressed_mul Xᴴ Y (P k)

omit [DecidableEq n] [DecidableEq kappa] in
private theorem unreadState_sub (X Y : Matrix n n ℂ) :
    unreadState P (X - Y) = unreadState P X - unreadState P Y := by
  classical
  simp [unreadState, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

omit [DecidableEq n] in
private theorem hilbert_schmidt_add_left (A B C : Matrix n n ℂ) :
    Matrix.trace ((A + B)ᴴ * C) =
      Matrix.trace (Aᴴ * C) + Matrix.trace (Bᴴ * C) := by
  simp [Matrix.add_mul]

omit [DecidableEq n] in
private theorem hilbert_schmidt_add_right (A B C : Matrix n n ℂ) :
    Matrix.trace (Aᴴ * (B + C)) =
      Matrix.trace (Aᴴ * B) + Matrix.trace (Aᴴ * C) := by
  simp [Matrix.mul_add]

omit [DecidableEq kappa] in
private theorem unreadState_hilbert_schmidt_orthogonal
    (hP : IsRecordMeasurement P) (X : Matrix n n ℂ) :
    Matrix.trace ((unreadState P X)ᴴ * (X - unreadState P X)) = 0 := by
  have hInner :
      Matrix.trace ((unreadState P X)ᴴ * X) =
        Matrix.trace ((unreadState P X)ᴴ * unreadState P X) := by
    calc
      Matrix.trace ((unreadState P X)ᴴ * X) =
          Matrix.trace ((unreadState P (unreadState P X))ᴴ * X) := by
        rw [unreadState_idempotent hP X]
      _ = Matrix.trace ((unreadState P X)ᴴ * unreadState P X) :=
        unreadState_hilbert_schmidt_self_adjoint hP (unreadState P X) X
  rw [Matrix.mul_sub, Matrix.trace_sub, hInner, sub_self]

omit [DecidableEq kappa] in
private theorem unreadState_hilbert_schmidt_pythagorean
    (hP : IsRecordMeasurement P) (X : Matrix n n ℂ) :
    hilbertSchmidtSquare X =
      hilbertSchmidtSquare (unreadState P X) +
        hilbertSchmidtSquare (X - unreadState P X) := by
  let discarded := X - unreadState P X
  have hDecomp : X = unreadState P X + discarded := by
    dsimp [discarded]
    abel
  have hDiscarded : unreadState P discarded = 0 := by
    dsimp [discarded]
    rw [unreadState_sub, unreadState_idempotent hP X, sub_self]
  have hReverseOrthogonal :
      Matrix.trace (discardedᴴ * unreadState P X) = 0 := by
    calc
      Matrix.trace (discardedᴴ * unreadState P X) =
          Matrix.trace ((unreadState P discarded)ᴴ * X) :=
        (unreadState_hilbert_schmidt_self_adjoint hP discarded X).symm
      _ = 0 := by rw [hDiscarded]; simp
  have hComplex :
      Matrix.trace (Xᴴ * X) =
        Matrix.trace ((unreadState P X)ᴴ * unreadState P X) +
          Matrix.trace (discardedᴴ * discarded) := by
    calc
      Matrix.trace (Xᴴ * X) =
          Matrix.trace ((unreadState P X + discarded)ᴴ *
            (unreadState P X + discarded)) :=
        congrArg (fun A => Matrix.trace (Aᴴ * A)) hDecomp
      _ = (Matrix.trace ((unreadState P X)ᴴ * unreadState P X) +
            Matrix.trace ((unreadState P X)ᴴ * discarded)) +
          (Matrix.trace (discardedᴴ * unreadState P X) +
            Matrix.trace (discardedᴴ * discarded)) := by
        rw [hilbert_schmidt_add_left, hilbert_schmidt_add_right,
          hilbert_schmidt_add_right]
      _ = Matrix.trace ((unreadState P X)ᴴ * unreadState P X) +
          Matrix.trace (discardedᴴ * discarded) := by
        rw [unreadState_hilbert_schmidt_orthogonal hP X, hReverseOrthogonal]
        ring
  unfold hilbertSchmidtSquare
  rw [hComplex, Complex.add_re]

omit [DecidableEq kappa] in
/-- For a finite complete family of pairwise orthogonal projections, discarding the record is
idempotent and Hilbert--Schmidt self-adjoint, its range is exactly the matrices with vanishing
cross blocks, and its retained and discarded components form an orthogonal Pythagorean split. -/
theorem unread_state_orthogonal_projection (hP : IsRecordMeasurement P) :
    (forall X, unreadState P (unreadState P X) = unreadState P X) /\
      (forall X Y, Matrix.trace ((unreadState P X)ᴴ * Y) =
        Matrix.trace (Xᴴ * unreadState P Y)) /\
      Set.range (unreadState P) =
        {X | forall i j, i ≠ j -> P i * X * P j = 0} /\
      (forall X, X = unreadState P X + (X - unreadState P X) /\
        Matrix.trace ((unreadState P X)ᴴ * (X - unreadState P X)) = 0) /\
      (forall X, hilbertSchmidtSquare X =
        hilbertSchmidtSquare (unreadState P X) +
          hilbertSchmidtSquare (X - unreadState P X)) := by
  refine ⟨unreadState_idempotent hP, unreadState_hilbert_schmidt_self_adjoint hP, ?_, ?_,
    unreadState_hilbert_schmidt_pythagorean hP⟩
  · ext X
    constructor
    · rintro ⟨Y, rfl⟩
      exact (unreadState_fixed_iff hP (unreadState P Y)).mp
        (unreadState_idempotent hP Y)
    · intro hBlocks
      exact ⟨X, (unreadState_fixed_iff hP X).mpr hBlocks⟩
  · intro X
    exact ⟨by abel, unreadState_hilbert_schmidt_orthogonal hP X⟩

#print axioms unread_state_orthogonal_projection

end D5.S3.Observer.Conditioning.UnreadStateOrthogonalProjection
