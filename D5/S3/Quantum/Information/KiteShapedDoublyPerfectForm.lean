/- GID: D5/S3/Quantum/Information/KiteShapedDoublyPerfectForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/KiteShapedDoublyPerfectForm
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Kite-shaped binary quadratic forms are doubly perfect exactly off one residue modulo three. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm

def kite (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if i.val + j.val + 2 ≤ n + 1 then 1 else 0

def quadraticForm (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks (kite n) 0 0 (kite n)

def symplecticForm (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks 0 1 (-1) 0

def TrivialKernel {ι : Type*} [Fintype ι] (M : Matrix ι ι (ZMod 2)) : Prop :=
  ∀ v, M.mulVec v = 0 → v = 0

def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (kite n).IsSymm ∧
    TrivialKernel (kite n) ∧ TrivialKernel (quadraticForm n) ∧
    (TrivialKernel (kite n * kite n - 1) ↔ n % 3 ≠ 1) ∧
    (TrivialKernel (quadraticForm n + symplecticForm n) ↔ n % 3 ≠ 1)

private def inverseKite (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => (if i.val + j.val + 1 = n then 1 else 0) +
    (if i.val + j.val + 2 = n then 1 else 0)

private def tridiagonal (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (i = j ∧ i.val ≠ 0) ∨ i.val + 1 = j.val ∨ j.val + 1 = i.val
    then 1 else 0

private lemma kernel_iff_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (ZMod 2)) : TrivialKernel M ↔ M.det ≠ 0 := by
  sorry

private lemma kite_symmetric (n : ℕ) : (kite n).IsSymm := by
  sorry

private lemma kite_inverse (n : ℕ) : kite n * inverseKite n = 1 := by
  sorry

private lemma kite_det (n : ℕ) : (kite n).det = 1 := by
  sorry

private lemma inverse_square (n : ℕ) :
    tridiagonal n = 1 + inverseKite n * inverseKite n := by
  sorry

private lemma tridiagonal_recurrence (n : ℕ) :
    (tridiagonal (n + 2)).det = (tridiagonal (n + 1)).det + (tridiagonal n).det := by
  sorry

private lemma tridiagonal_det_zero (n : ℕ) : (tridiagonal n).det = 0 ↔ n % 3 = 1 := by
  sorry

private lemma square_det (n : ℕ) :
    (kite n * kite n - 1).det = (tridiagonal n).det := by
  sorry

private lemma quadratic_det (n : ℕ) : (quadraticForm n).det = 1 := by
  sorry

private lemma symplectic_det (n : ℕ) :
    (quadraticForm n + symplecticForm n).det = (kite n * kite n - 1).det := by
  sorry

theorem result : claim := by
  intro n _hn
  refine ⟨kite_symmetric n, (kernel_iff_det _).2 ?_, (kernel_iff_det _).2 ?_, ?_, ?_⟩
  · rw [kite_det]
    exact one_ne_zero
  · rw [quadratic_det]
    exact one_ne_zero
  · rw [kernel_iff_det, square_det, ne_eq, tridiagonal_det_zero]
  · rw [kernel_iff_det, symplectic_det, square_det, ne_eq, tridiagonal_det_zero]

end D5.S3.Quantum.Information.KiteShapedDoublyPerfectForm
