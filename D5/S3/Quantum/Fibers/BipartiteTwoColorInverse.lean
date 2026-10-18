/- GID: D5/S3/Quantum/Fibers/BipartiteTwoColorInverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/BipartiteTwoColorInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The five independent configurations of P₃ satisfy the exchange double-commutator identity, and two color-scaled accelerations invert the blocking coordinate.
-/

import Mathlib

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Quantum.Fibers.BipartiteTwoColorInverse

def commutator {n : Type} [Fintype n] (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

def doubleCommutator {n : Type} [Fintype n] (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  commutator A (commutator A B)

/- The five independent sets are ordered as `∅, {u}, {w}, {v}, {u,w}`. -/
def p3Hamiltonian (Ωu Ωv Ωw : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, Ωu, Ωw, Ωv, 0;
     Ωu, 0, 0, 0, Ωw;
     Ωw, 0, 0, 0, Ωu;
     Ωv, 0, 0, 0, 0;
     0, Ωw, Ωu, 0, 0]

def occupationV : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 0]

def blockingV : Matrix (Fin 5) (Fin 5) ℂ :=
  !![1, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 0]

def exchangeUV : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 0, 0, 0]

def exchangeVW : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 0, 0]

/-- Direct finite verification of the P₃ exchange identity. -/
theorem p3_double_commutator (Ωu Ωv Ωw : ℂ) :
    doubleCommutator (p3Hamiltonian Ωu Ωv Ωw) occupationV =
      (2 * Ωv ^ 2) • (2 • occupationV - blockingV) +
        (Ωu * Ωv) • exchangeUV + (Ωv * Ωw) • exchangeVW := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doubleCommutator, commutator, p3Hamiltonian, occupationV,
      blockingV, exchangeUV, exchangeVW, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

/-- The A-color formula: doubling the A-color doubles exchanges and quadruples
the diagonal term, so the blocking coordinate is recovered by subtraction. -/
theorem two_color_inverse_A (m b a a' Ω : ℝ)
    (h₁ : a = -(2 * Ω ^ 2 * (2 * m - b) + 1))
    (h₂ : a' = -(8 * Ω ^ 2 * (2 * m - b) + 2))
    (hΩ : Ω ≠ 0) :
    b = 2 * m + (a' - 2 * a) / (4 * Ω ^ 2) := by
  field_simp [hΩ]
  linarith

/-- The B-color formula: doubling the neighboring A-color doubles exchanges
while preserving the diagonal term. -/
theorem two_color_inverse_B (m b a a' Ω : ℝ)
    (h₁ : a = -(2 * Ω ^ 2 * (2 * m - b) + 1))
    (h₂ : a' = -(2 * Ω ^ 2 * (2 * m - b) + 2))
    (hΩ : Ω ≠ 0) :
    b = 2 * m + (2 * a - a') / (2 * Ω ^ 2) := by
  field_simp [hΩ]
  linarith

end D5.S3.Quantum.Fibers.BipartiteTwoColorInverse
