/- GID: D5/S3/Arithmetic/HigherOrderFourier/FiniteGowersCubeMoment
   generality: G
   mirror-B: D5/B/S3/Arithmetic/HigherOrderFourier/FiniteGowersCubeMoment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Iterated multiplicative derivatives define manifestly nonnegative finite Gowers correlation energies. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Finite Gowers derivative energies

For a complex-valued function on a finite additive group, the multiplicative
derivative is

`Delta_h f(x) = f(x+h) conj(f(x))`.

Iterating these derivatives along a finite direction list produces the cube
phase underlying Gowers uniformity.  This module defines the corresponding
manifestly nonnegative correlation energy

`sum_h |sum_x Delta_h1 ... Delta_hd f(x)|^2`.

At depth one this is the unnormalized fourth power of the finite `U^2`
seminorm.  The energy vanishes exactly when every iterated correlation
vanishes.

This file does not prove the Gowers-Cauchy-Schwarz inequality, a norm theorem,
a Fourier identity, an inverse theorem, or nilsequence correlation.  Those are
separate layers.
-/

/- Library-search audit trail (2026-09-01):
   * Repository search found no Gowers norm, cube moment, or multiplicative
     derivative owner.
   * Existing Fourier modules treat linear characters and window diffraction.
   * Pinned Mathlib supplies finite sums, complex conjugation, and finite
     function types. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Arithmetic.HigherOrderFourier.FiniteGowersCubeMoment

noncomputable section

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- Multiplicative derivative in one additive direction. -/
def multiplicativeDerivative
    (function : G → ℂ) (direction : G) : G → ℂ :=
  fun point => function (point + direction) * star (function point)

/-- Iterated multiplicative derivative along an ordered direction list. -/
def iteratedDerivative : List G → (G → ℂ) → (G → ℂ)
  | [], function => function
  | direction :: directions, function =>
      iteratedDerivative directions
        (multiplicativeDerivative function direction)

/-- Unnormalized correlation of an iterated derivative. -/
def iteratedCorrelation
    (directions : List G) (function : G → ℂ) : ℂ :=
  ∑ point, iteratedDerivative directions function point

/-- Manifestly nonnegative finite cube correlation energy at derivative depth
`depth`. -/
def finiteGowersDerivativeEnergy
    (depth : ℕ) (function : G → ℂ) : ℝ :=
  ∑ directions : Fin depth → G,
    ‖iteratedCorrelation (List.ofFn directions) function‖ ^ 2

/-- Unnormalized finite `U^2` fourth-power energy. -/
def finiteGowersU2Energy (function : G → ℂ) : ℝ :=
  ∑ direction : G,
    ‖∑ point, multiplicativeDerivative function direction point‖ ^ 2

/-- Iterating over an appended direction list means applying the earlier
block and then the later block. -/
theorem iteratedDerivative_append
    (earlier later : List G) (function : G → ℂ) :
    iteratedDerivative (earlier ++ later) function =
      iteratedDerivative later (iteratedDerivative earlier function) := by
  induction earlier generalizing function with
  | nil =>
      rfl
  | cons direction earlier inductionHypothesis =>
      simp only [List.cons_append, iteratedDerivative]
      exact inductionHypothesis
        (multiplicativeDerivative function direction)

/-- Multiplicative derivatives preserve pointwise products. -/
theorem multiplicativeDerivative_mul
    (first second : G → ℂ) (direction : G) :
    multiplicativeDerivative (first * second) direction =
      multiplicativeDerivative first direction *
        multiplicativeDerivative second direction := by
  funext point
  simp [multiplicativeDerivative]
  ring

/-- The multiplicative derivative of the zero function is zero. -/
theorem multiplicativeDerivative_zero (direction : G) :
    multiplicativeDerivative (0 : G → ℂ) direction = 0 := by
  funext point
  simp [multiplicativeDerivative]

/-- Every finite derivative energy is nonnegative. -/
theorem finiteGowersDerivativeEnergy_nonneg
    (depth : ℕ) (function : G → ℂ) :
    0 ≤ finiteGowersDerivativeEnergy depth function := by
  unfold finiteGowersDerivativeEnergy
  exact Finset.sum_nonneg fun directions _ => sq_nonneg _

/-- The finite `U^2` energy is nonnegative. -/
theorem finiteGowersU2Energy_nonneg (function : G → ℂ) :
    0 ≤ finiteGowersU2Energy function := by
  unfold finiteGowersU2Energy
  exact Finset.sum_nonneg fun direction _ => sq_nonneg _

/-- The zero function has zero derivative energy at every positive depth. -/
theorem finiteGowersDerivativeEnergy_zero
    (depth : ℕ) (hDepth : 0 < depth) :
    finiteGowersDerivativeEnergy depth (0 : G → ℂ) = 0 := by
  unfold finiteGowersDerivativeEnergy iteratedCorrelation
  apply Finset.sum_eq_zero
  intro directions _
  have hList : List.ofFn directions ≠ [] := by
    intro hEmpty
    have hLength := congrArg List.length hEmpty
    simp at hLength
    omega
  cases hDirections : List.ofFn directions with
  | nil => exact (hList hDirections).elim
  | cons direction rest =>
      simp [iteratedDerivative, multiplicativeDerivative_zero]

/-- The zero function has zero finite `U^2` energy. -/
theorem finiteGowersU2Energy_zero :
    finiteGowersU2Energy (0 : G → ℂ) = 0 := by
  simp [finiteGowersU2Energy, multiplicativeDerivative]

/-- Zero finite `U^2` energy is equivalent to vanishing of every directional
correlation. -/
theorem finiteGowersU2Energy_eq_zero_iff
    (function : G → ℂ) :
    finiteGowersU2Energy function = 0 ↔
      ∀ direction : G,
        (∑ point, multiplicativeDerivative function direction point) = 0 := by
  constructor
  · intro hEnergy direction
    have hTermLe :
        ‖∑ point, multiplicativeDerivative function direction point‖ ^ 2 ≤
          finiteGowersU2Energy function := by
      unfold finiteGowersU2Energy
      exact Finset.single_le_sum
        (fun other _ => sq_nonneg
          ‖∑ point, multiplicativeDerivative function other point‖)
        (Finset.mem_univ direction)
    rw [hEnergy] at hTermLe
    have hNormSq :
        ‖∑ point, multiplicativeDerivative function direction point‖ ^ 2 = 0 :=
      le_antisymm hTermLe (sq_nonneg _)
    have hNorm :
        ‖∑ point, multiplicativeDerivative function direction point‖ = 0 := by
      nlinarith [norm_nonneg
        (∑ point, multiplicativeDerivative function direction point)]
    exact norm_eq_zero.mp hNorm
  · intro hCorrelation
    unfold finiteGowersU2Energy
    apply Finset.sum_eq_zero
    intro direction _
    rw [hCorrelation direction]
    norm_num

/-- Depth-one derivative energy is exactly the finite `U^2` energy. -/
theorem finiteGowersDerivativeEnergy_one
    (function : G → ℂ) :
    finiteGowersDerivativeEnergy 1 function =
      finiteGowersU2Energy function := by
  classical
  unfold finiteGowersDerivativeEnergy finiteGowersU2Energy
  let equivalence : (Fin 1 → G) ≃ G :=
    { toFun := fun directions => directions 0
      invFun := fun direction _ => direction
      left_inv := by intro directions; funext index; fin_cases index; rfl
      right_inv := by intro direction; rfl }
  rw [← equivalence.sum_comp]
  apply Finset.sum_congr rfl
  intro directions _
  change
    ‖iteratedCorrelation (List.ofFn directions) function‖ ^ 2 =
      ‖∑ point, multiplicativeDerivative function (directions 0) point‖ ^ 2
  congr 2
  simp [iteratedCorrelation, iteratedDerivative, List.ofFn]

example :
    finiteGowersU2Energy (0 : ZMod 2 → ℂ) = 0 :=
  finiteGowersU2Energy_zero

#print axioms iteratedDerivative_append
#print axioms multiplicativeDerivative_mul
#print axioms finiteGowersDerivativeEnergy_nonneg
#print axioms finiteGowersU2Energy_nonneg
#print axioms finiteGowersDerivativeEnergy_zero
#print axioms finiteGowersU2Energy_eq_zero_iff
#print axioms finiteGowersDerivativeEnergy_one

end

end D5.S3.Arithmetic.HigherOrderFourier.FiniteGowersCubeMoment
