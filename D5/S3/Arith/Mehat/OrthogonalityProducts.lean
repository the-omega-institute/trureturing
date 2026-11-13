/- GID: D5/S3/Arith/Mehat/OrthogonalityProducts
   generality: G
   mirror-B: D5/B/S3/Arith/Mehat/OrthogonalityProducts
   mirror-E: none
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Funext]
   utility: none
   digest: Integer quaternion factors with distinct indexed squared-entry products. -/

import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Mehat.OrthogonalityProducts

open scoped BigOperators
open MvPolynomial Matrix

/-- The exact positive-`k` assertion of Mehat, Problem 9.2. -/
def Problem92 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ (A : Fin k → Matrix (Fin 3) (Fin 3) ℤ) (gamma : Fin k → ℤ),
    (∀ i, gamma i ≠ 0 ∧ A i * (A i)ᵀ = gamma i • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ∧
    Function.Injective (fun p : Fin k → Fin 3 × Fin 3 => ∏ i, (A i (p i).1 (p i).2) ^ 2)

/-- The exact unbounded order assertion of Mehat, Problem 9.1. -/
def Problem91 : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ (M : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℤ) (gamma : ℤ),
    gamma ≠ 0 ∧ M * Mᵀ = gamma • (1 : Matrix (Fin (3 ^ k)) (Fin (3 ^ k)) ℤ) ∧
    (∑ i, M i i ^ 2) = gamma ∧ (∑ i, M i i.rev ^ 2) = gamma ∧
    Function.Injective (fun p : Fin (3 ^ k) × Fin (3 ^ k) => (M p.1 p.2) ^ 2)

/-- Quaternion parametrization of the nine entries, with no diagonal requirement on a factor. -/
def quaternionMatrix {R : Type*} [CommRing R] (a : Fin 4 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![a 0 ^ 2 + a 1 ^ 2 - a 2 ^ 2 - a 3 ^ 2, 2 * (a 1 * a 2 - a 0 * a 3), 2 * (a 1 * a 3 + a 0 * a 2);
     2 * (a 1 * a 2 + a 0 * a 3), a 0 ^ 2 - a 1 ^ 2 + a 2 ^ 2 - a 3 ^ 2, 2 * (a 2 * a 3 - a 0 * a 1);
     2 * (a 1 * a 3 - a 0 * a 2), 2 * (a 2 * a 3 + a 0 * a 1), a 0 ^ 2 - a 1 ^ 2 - a 2 ^ 2 + a 3 ^ 2]

private def entry (p : Fin 3 × Fin 3) : MvPolynomial (Fin 4) ℤ :=
  quaternionMatrix (fun i => X i) p.1 p.2

private theorem eval_entry (a : Fin 4 → ℤ) (p : Fin 3 × Fin 3) :
    eval a (entry p) = quaternionMatrix a p.1 p.2 := by
  rcases p with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [entry, quaternionMatrix]

private theorem integer_nonzero_point {σ : Type*} (p : MvPolynomial σ ℤ) (hp : p ≠ 0) :
    ∃ a : σ → ℤ, eval a p ≠ 0 := by
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro a
  simpa using not_not.mp (fun ha => h ⟨a, ha⟩)

end D5.S3.Arith.Mehat.OrthogonalityProducts
