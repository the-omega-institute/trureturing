/- GID: D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory
   mirror-E: none(waiver:exact-matrix-identities)
   anchors: []
   utility: none
   digest: For a self-adjoint finite transfer matrix and an orthogonal projection,
     the two-step compression defect is a Gram matrix and vanishes exactly at closure. -/

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

set_option autoImplicit false

open scoped Matrix

namespace D5.S3.Observer.ProbabilisticClosure.ReversibleProjectionMemory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The one-step dynamics restricted back to the observed linear subspace. -/
def compressed (P K : Matrix n n Real) : Matrix n n Real := P * K * P

/-- Exact two-step dynamics minus two independently compressed one-step updates. -/
def defect (P K : Matrix n n Real) : Matrix n n Real :=
  P * (K * K) * P - compressed P K * compressed P K

/-- The component of a one-step propagated observed observable that becomes hidden. -/
def leakage (P K : Matrix n n Real) : Matrix n n Real := (1 - P) * K * P

private theorem complement_idempotent (P : Matrix n n Real) (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  calc
    (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P := by rw [hP]; abel

/-- The hidden round trip is exactly the Chapman--Kolmogorov compression defect.
No stochasticity is required for this purely operator identity. -/
theorem defect_eq_hidden_roundtrip (P K : Matrix n n Real) (hP : P * P = P) :
    defect P K = P * K * (1 - P) * K * P := by
  have hprod : compressed P K * compressed P K = P * K * P * K * P := by
    calc
      compressed P K * compressed P K = P * K * (P * P) * K * P := by
        simp only [compressed, mul_assoc]
      _ = P * K * P * K * P := by rw [hP]
  rw [defect, hprod]
  noncomm_ring

/-- Reversibility/self-adjointness prevents cancellation of hidden leakage.
For a nonuniform reversible chain this applies after conjugating to L2(pi)
orthonormal coordinates, a separate identification not assumed by this theorem. -/
theorem defect_eq_leakage_gram (P K : Matrix n n Real)
    (hP : P * P = P) (hPs : Pᴴ = P) (hKs : Kᴴ = K) :
    defect P K = (leakage P K)ᴴ * leakage P K := by
  have hstar : (leakage P K)ᴴ = P * K * (1 - P) := by
    simp only [leakage, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hPs, hKs, mul_assoc]
  rw [defect_eq_hidden_roundtrip P K hP, hstar, leakage]
  symm
  calc
    (P * K * (1 - P)) * ((1 - P) * K * P) =
        P * K * ((1 - P) * (1 - P)) * K * P := by simp only [mul_assoc]
    _ = P * K * (1 - P) * K * P := by rw [complement_idempotent P hP]

/-- A zero two-step defect is equivalent to exact invariance of the observed
subspace. This implication is stronger than an unqualified semigroup fit. -/
theorem two_step_closure_iff (P K : Matrix n n Real)
    (hP : P * P = P) (hPs : Pᴴ = P) (hKs : Kᴴ = K) :
    defect P K = 0 ↔ K * P = P * K * P := by
  rw [defect_eq_leakage_gram P K hP hPs hKs,
    Matrix.conjTranspose_mul_self_eq_zero]
  have hleak : leakage P K = K * P - P * K * P := by
    unfold leakage
    noncomm_ring
  rw [hleak, sub_eq_zero]

/-- Once the observed subspace is invariant, every positive integer time is
exactly represented by a power of the same compressed one-step operator. -/
theorem compressed_positive_powers (P K : Matrix n n Real)
    (hInv : K * P = P * K * P) (t : Nat) :
    P * K ^ (t + 1) * P = (compressed P K) ^ (t + 1) := by
  induction t with
  | zero => simp [compressed]
  | succ t ih =>
    calc
      P * K ^ (t + 1 + 1) * P = P * K ^ (t + 1) * (K * P) := by
        rw [pow_succ]
        simp only [mul_assoc]
      _ = P * K ^ (t + 1) * (P * K * P) := by rw [hInv]
      _ = (P * K ^ (t + 1) * P) * (K * P) := by simp only [mul_assoc]
      _ = (compressed P K) ^ (t + 1) * (compressed P K) := by
        rw [ih, hInv]
        rfl
      _ = (compressed P K) ^ (t + 1 + 1) := (pow_succ _ _).symm

/-- For reversible finite operators, exact agreement at two steps is equivalent
to the entire positive-integer compressed semigroup law. -/
theorem two_steps_iff_all_positive_times (P K : Matrix n n Real)
    (hP : P * P = P) (hPs : Pᴴ = P) (hKs : Kᴴ = K) :
    defect P K = 0 ↔
      ∀ t : Nat, P * K ^ (t + 1) * P = (compressed P K) ^ (t + 1) := by
  constructor
  · intro h t
    exact compressed_positive_powers P K ((two_step_closure_iff P K hP hPs hKs).mp h) t
  · intro h
    have ht := h 1
    simpa only [defect, pow_two, sub_eq_zero] using ht

#print axioms defect_eq_leakage_gram
#print axioms two_step_closure_iff
#print axioms compressed_positive_powers
#print axioms two_steps_iff_all_positive_times

end D5.S3.Observer.ProbabilisticClosure.ReversibleProjectionMemory
