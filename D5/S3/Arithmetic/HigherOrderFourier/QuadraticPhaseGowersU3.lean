/- GID: D5/S3/Arithmetic/HigherOrderFourier/QuadraticPhaseGowersU3
   generality: G
   mirror-B: D5/B/S3/Arithmetic/HigherOrderFourier/QuadraticPhaseGowersU3
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit quadratic phases have constant second multiplicative derivatives and maximal finite U3 energy. -/

import D5.S3.Arithmetic.HigherOrderFourier.GowersTranslationModulationInvariance
import Mathlib.Tactic

/-!
# Quadratic phases and finite U3 energy

The unnormalized finite `U^3` energy is the sum, over two additive directions,
of the squared norm of the correlation of the second multiplicative
derivative.  A unit quadratic phase is characterized here by the exact finite
property that every second derivative is independent of the base point and
has unit norm.

Such a phase has maximal energy `|G|^4`.  Every unitary additive character is
a degenerate quadratic phase because its first derivative is constant and its
second derivative is one.

This module does not classify quadratic polynomials on arbitrary finite
groups, prove the `U^3` inverse theorem, or construct nilsequences.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteGowersCubeMoment` owns iterated multiplicative derivatives.
   * `GowersTranslationModulationInvariance` owns unitary additive characters
     and their first-derivative formula.
   * Repository search found no finite `U^3` energy or quadratic-phase
     characterization.
   * Pinned Mathlib supplies finite sums and norm multiplication. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Arithmetic.HigherOrderFourier.QuadraticPhaseGowersU3

open D5.S3.Arithmetic.HigherOrderFourier.FiniteGowersCubeMoment
open D5.S3.Arithmetic.HigherOrderFourier.GowersTranslationModulationInvariance

noncomputable section

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- Unnormalized finite `U^3` eighth-power energy. -/
def finiteGowersU3Energy (function : G → ℂ) : ℝ :=
  ∑ firstDirection : G, ∑ secondDirection : G,
    ‖∑ point,
      iteratedDerivative [firstDirection, secondDirection] function point‖ ^ 2

/-- A unit quadratic phase has base-point independent unit second
derivatives. -/
def IsUnitQuadraticPhase (function : G → ℂ) : Prop :=
  ∃ secondPhase : G → G → ℂ,
    (∀ firstDirection secondDirection point,
      iteratedDerivative [firstDirection, secondDirection] function point =
        secondPhase firstDirection secondDirection) ∧
    ∀ firstDirection secondDirection,
      ‖secondPhase firstDirection secondDirection‖ = 1

/-- Finite `U^3` energy is nonnegative. -/
theorem finiteGowersU3Energy_nonneg (function : G → ℂ) :
    0 ≤ finiteGowersU3Energy function := by
  unfold finiteGowersU3Energy
  exact Finset.sum_nonneg fun firstDirection _ =>
    Finset.sum_nonneg fun secondDirection _ => sq_nonneg _

/-- Unit quadratic phases have maximal unnormalized finite `U^3` energy. -/
theorem finiteGowersU3Energy_eq_card_pow_four_of_quadratic
    (function : G → ℂ) (hQuadratic : IsUnitQuadraticPhase function) :
    finiteGowersU3Energy function = (Fintype.card G : ℝ) ^ 4 := by
  rcases hQuadratic with ⟨secondPhase, hConstant, hNorm⟩
  unfold finiteGowersU3Energy
  calc
    (∑ firstDirection : G, ∑ secondDirection : G,
        ‖∑ point,
          iteratedDerivative [firstDirection, secondDirection]
            function point‖ ^ 2) =
      ∑ firstDirection : G, ∑ secondDirection : G,
        (Fintype.card G : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro firstDirection _
      apply Finset.sum_congr rfl
      intro secondDirection _
      have hCorrelation :
          (∑ point,
              iteratedDerivative [firstDirection, secondDirection]
                function point) =
            (Fintype.card G : ℂ) *
              secondPhase firstDirection secondDirection := by
        simp_rw [hConstant firstDirection secondDirection]
        simp
      rw [hCorrelation, norm_mul, hNorm, mul_one]
      simp
    _ = (Fintype.card G : ℝ) ^ 4 := by
      simp
      ring

/-- Every unitary additive character is a unit quadratic phase. -/
theorem additiveCharacter_isUnitQuadraticPhase
    (character : FiniteUnitaryAdditiveCharacter (G := G)) :
    IsUnitQuadraticPhase character.value := by
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · intro firstDirection secondDirection point
    have hFirstDerivative :
        multiplicativeDerivative character.value firstDirection =
          fun _ => character.value firstDirection := by
      funext basePoint
      exact multiplicativeDerivative_character character
        firstDirection basePoint
    change
      multiplicativeDerivative
          (multiplicativeDerivative character.value firstDirection)
          secondDirection point = 1
    rw [hFirstDerivative]
    simp [multiplicativeDerivative, character.mul_star]
  · intro firstDirection secondDirection
    simp

/-- Every unitary additive character has maximal finite `U^3` energy. -/
theorem finiteGowersU3Energy_character
    (character : FiniteUnitaryAdditiveCharacter (G := G)) :
    finiteGowersU3Energy character.value =
      (Fintype.card G : ℝ) ^ 4 := by
  exact finiteGowersU3Energy_eq_card_pow_four_of_quadratic
    character.value (additiveCharacter_isUnitQuadraticPhase character)

/-- The zero function has zero finite `U^3` energy. -/
theorem finiteGowersU3Energy_zero :
    finiteGowersU3Energy (0 : G → ℂ) = 0 := by
  simp [finiteGowersU3Energy, iteratedDerivative,
    multiplicativeDerivative]

example :
    finiteGowersU3Energy (0 : ZMod 2 → ℂ) = 0 :=
  finiteGowersU3Energy_zero

#print axioms finiteGowersU3Energy_nonneg
#print axioms finiteGowersU3Energy_eq_card_pow_four_of_quadratic
#print axioms additiveCharacter_isUnitQuadraticPhase
#print axioms finiteGowersU3Energy_character
#print axioms finiteGowersU3Energy_zero

end

end D5.S3.Arithmetic.HigherOrderFourier.QuadraticPhaseGowersU3
