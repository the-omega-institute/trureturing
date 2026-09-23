/- GID: D5/S3/Quantum/Reduction/SourceAwareSchur
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/SourceAwareSchur
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Source-aware Schur reduction preserves response, kernels, and graph metrics. -/

import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Source-aware block elimination

Library-first: `Matrix.invOf_fromBlocks₂₂_eq` supplies the block inverse and the
existing repository `SchurMinimum` and `SchurComplementAssociativity` remain the
owners of their separate results. This file adds their source/gauge/graph
consumers; it does not reprove determinant factorisation or Schur associativity.
All inverses below are genuine `Invertible` instances. No pseudoinverse identity
is silently extended to a singular block, and no differentiation of a resolvent
is claimed by an algebraic identity.
-/

noncomputable section
open scoped Matrix ComplexOrder

namespace D5.S3.Quantum.Reduction.SourceAwareSchur

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m n r t : Type*}
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

/-- Two independently chosen probes retain the exact bilinear response, including its hidden-source term. -/
theorem source_preserving_schur
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) [Invertible D] [Invertible (A - B * ⅟D * C)]
    [Invertible (Matrix.fromBlocks A B C D)]
    (Jv : Matrix r m ℂ) (Jh : Matrix r n ℂ)
    (Kv : Matrix m t ℂ) (Kh : Matrix n t ℂ) :
    Matrix.fromCols Jv Jh * ⅟(Matrix.fromBlocks A B C D) * Matrix.fromRows Kv Kh =
      (Jv - Jh * ⅟D * C) * ⅟(A - B * ⅟D * C) * (Kv - B * ⅟D * Kh) +
        Jh * ⅟D * Kh := by
  rw [Matrix.invOf_fromBlocks₂₂_eq, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

/-- The full operator applied to the Schur graph has zero hidden component. -/
theorem schur_graph_lift
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) [Invertible D] :
    Matrix.fromBlocks A B C D * Matrix.fromRows (1 : Matrix m m ℂ) (-(⅟D * C)) =
      Matrix.fromRows (A - B * ⅟D * C) (0 : Matrix n m ℂ) := by
  have hcancel : D * (⅟D * C) = C := by
    rw [← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  rw [Matrix.fromBlocks_mul_fromRows]
  simp only [Matrix.mul_one, Matrix.mul_neg, hcancel, add_neg_cancel,
    Matrix.mul_assoc, sub_eq_add_neg]

/-- Kernel generators and invariant sources descend together; the hidden component is solved, not supplied. -/
theorem gauge_and_source_descent
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) [Invertible D]
    (Rv : Matrix m t ℂ) (Rh : Matrix n t ℂ)
    (Jv : Matrix r m ℂ) (Jh : Matrix r n ℂ)
    (hvisible : A * Rv + B * Rh = 0)
    (hhidden : C * Rv + D * Rh = 0)
    (hsource : Jv * Rv + Jh * Rh = 0) :
    Rh = -(⅟D * C * Rv) ∧
      (A - B * ⅟D * C) * Rv = 0 ∧ (Jv - Jh * ⅟D * C) * Rv = 0 := by
  have hcancel : ⅟D * (D * Rh) = Rh := by
    rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
  have hh : ⅟D * C * Rv + Rh = 0 := by
    have h := congrArg (fun X => ⅟D * X) hhidden
    simpa only [Matrix.mul_add, hcancel, Matrix.mul_zero, Matrix.mul_assoc] using h
  have hr : Rh = -(⅟D * C * Rv) := by
    calc
      Rh = (⅟D * C * Rv + Rh) - ⅟D * C * Rv := by abel
      _ = -(⅟D * C * Rv) := by rw [hh]; simp
  refine ⟨hr, ?_, ?_⟩
  · rw [hr] at hvisible
    simpa only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]
      using hvisible
  · rw [hr] at hsource
    simpa only [Matrix.sub_mul, Matrix.mul_neg, Matrix.mul_assoc, sub_eq_add_neg]
      using hsource

/-- A graph frame has the genuine pullback norm I + X-adjoint X. -/
theorem graph_gram (X : Matrix n m ℂ) :
    (Matrix.fromRows (1 : Matrix m m ℂ) X)ᴴ * Matrix.fromRows 1 X = 1 + Xᴴ * X := by
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows]
  simp

/-- The graph norm is positive definite for every X, without an unproved invertibility hypothesis. -/
theorem graph_gram_positive (X : Matrix n m ℂ) : (1 + Xᴴ * X).PosDef := by
  rw [← graph_gram X]
  apply Matrix.PosDef.conjTranspose_mul_self
  intro v w h
  funext i
  have hi := congrFun h (Sum.inl i)
  simpa only [Matrix.fromRows_mulVec, Matrix.one_mulVec, Sum.elim_inl] using hi

/-- The Riccati equation is exactly the invariant graph equation. -/
theorem riccati_intertwines
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (X : Matrix n m ℂ)
    (hX : C + D * X = X * (A + B * X)) :
    Matrix.fromBlocks A B C D * Matrix.fromRows (1 : Matrix m m ℂ) X =
      Matrix.fromRows (1 : Matrix m m ℂ) X * (A + B * X) := by
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  simp only [Matrix.mul_one, Matrix.one_mul, hX]

/-- A self-adjoint full operator induces a Gram-self-adjoint reduced operator. -/
theorem intertwined_gram_selfadjoint
    (H : Matrix n n ℂ) (L : Matrix n m ℂ) (K : Matrix m m ℂ)
    (hH : Hᴴ = H) (hHL : H * L = L * K) :
    (Lᴴ * L) * K = Kᴴ * (Lᴴ * L) := by
  have hs : Lᴴ * H = Kᴴ * Lᴴ := by
    simpa only [Matrix.conjTranspose_mul, hH] using congrArg Matrix.conjTranspose hHL
  calc
    _ = Lᴴ * (L * K) := Matrix.mul_assoc _ _ _
    _ = Lᴴ * (H * L) := by rw [← hHL]
    _ = (Lᴴ * H) * L := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [hs, Matrix.mul_assoc]

/-- The graph equation's entire failure is its explicit hidden Riccati residual. -/
theorem riccati_residual
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ)
    (D : Matrix n n ℂ) (X : Matrix n m ℂ) :
    Matrix.fromBlocks A B C D * Matrix.fromRows (1 : Matrix m m ℂ) X -
      Matrix.fromRows (1 : Matrix m m ℂ) X * (A + B * X) =
    Matrix.fromRows (0 : Matrix m m ℂ) (C + D * X - X * (A + B * X)) := by
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]
  ext (i | i) j <;> simp

/-- Projection can destroy nilpotency; this is the exact discarded-excursion defect in any ring. -/
theorem projected_nilpotency_defect {R : Type*} [Ring R]
    (P Q : R) (hP : P * P = P) (hQ : Q * Q = 0) :
    (P * Q * P) * (P * Q * P) = -(P * Q * (1 - P) * Q * P) := by
  have hzero : P * Q * Q * P = 0 := by
    calc
      _ = P * (Q * Q) * P := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  calc
    _ = P * Q * (P * P) * Q * P := by noncomm_ring
    _ = P * Q * P * Q * P := by rw [hP]
    _ = P * Q * P * Q * P - P * Q * Q * P := by rw [hzero, sub_zero]
    _ = _ := by noncomm_ring

/-- A rational four-state witness rules out an unconditional projected-nilpotency claim. -/
theorem projected_nilpotency_counterexample :
    let Q : Matrix (Fin 4) (Fin 4) ℚ :=
      !![0, 0, 0, 0; 1, 0, 0, 0; 1, 0, 0, 0; 0, 1, -1, 0]
    let P : Matrix (Fin 4) (Fin 4) ℚ :=
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1]
    Q * Q = 0 ∧ P * P = P ∧ (P * Q * P) * (P * Q * P) ≠ 0 := by
  decide

#print axioms source_preserving_schur
#print axioms schur_graph_lift
#print axioms gauge_and_source_descent
#print axioms graph_gram
#print axioms graph_gram_positive
#print axioms riccati_intertwines
#print axioms intertwined_gram_selfadjoint
#print axioms riccati_residual
#print axioms projected_nilpotency_defect
#print axioms projected_nilpotency_counterexample

end D5.S3.Quantum.Reduction.SourceAwareSchur
