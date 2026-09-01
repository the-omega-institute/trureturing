/- GID: D5/S3/Arithmetic/HigherOrderFourier/GowersTranslationModulationInvariance
   generality: G
   mirror-B: D5/B/S3/Arithmetic/HigherOrderFourier/GowersTranslationModulationInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite U2 derivative energy is invariant under additive translation and unitary-character modulation. -/

import D5.S3.Arithmetic.HigherOrderFourier.FiniteGowersCubeMoment
import Mathlib.Tactic

/-!
# Gowers translation and modulation invariance

The finite `U^2` derivative energy is unchanged when a function is translated
on its finite additive group.  It is also unchanged by multiplication with a
unitary additive character.  The second statement follows because the
multiplicative derivative of a character is the constant phase carried by the
direction, and this phase has unit norm.

This module gives the basic affine symmetries of the finite `U^2` energy.  It
does not prove the Fourier fourth-moment identity or a higher-order inverse
theorem.
-/

/- Library-search audit trail (2026-09-01):
   * `FiniteGowersCubeMoment` owns multiplicative derivatives and finite `U^2`
     energy.
   * Repository search found no additive-character structure or invariance
     theorem for a Gowers energy.
   * Pinned Mathlib supplies finite equivalence reindexing and complex norm
     multiplicativity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Arithmetic.HigherOrderFourier.GowersTranslationModulationInvariance

open D5.S3.Arithmetic.HigherOrderFourier.FiniteGowersCubeMoment

noncomputable section

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G]

/-- Translation of a complex function on an additive group. -/
def translateFunction (shift : G) (function : G → ℂ) : G → ℂ :=
  fun point => function (point + shift)

/-- A unitary complex additive character, recorded in the exact form needed by
finite derivative calculations. -/
structure FiniteUnitaryAdditiveCharacter where
  value : G → ℂ
  map_zero : value 0 = 1
  map_add : ∀ first second,
    value (first + second) = value first * value second
  norm_one : ∀ point, ‖value point‖ = 1
  mul_star : ∀ point, value point * star (value point) = 1

/-- Modulation by a unitary additive character. -/
def modulateFunction
    (character : FiniteUnitaryAdditiveCharacter (G := G))
    (function : G → ℂ) : G → ℂ :=
  fun point => character.value point * function point

/-- Translation moves the evaluation point of every multiplicative
derivative. -/
theorem multiplicativeDerivative_translate
    (function : G → ℂ) (shift direction point : G) :
    multiplicativeDerivative (translateFunction shift function)
        direction point =
      multiplicativeDerivative function direction (point + shift) := by
  simp [multiplicativeDerivative, translateFunction,
    add_assoc, add_left_comm, add_comm]

/-- Directional correlation is invariant under translating the function. -/
theorem directionalCorrelation_translate
    (function : G → ℂ) (shift direction : G) :
    (∑ point,
        multiplicativeDerivative (translateFunction shift function)
          direction point) =
      ∑ point, multiplicativeDerivative function direction point := by
  simp_rw [multiplicativeDerivative_translate]
  let translation : G ≃ G := Equiv.addRight shift
  simpa [translation] using
    translation.sum_comp
      (fun point => multiplicativeDerivative function direction point)

/-- Finite `U^2` derivative energy is translation invariant. -/
theorem finiteGowersU2Energy_translate
    (function : G → ℂ) (shift : G) :
    finiteGowersU2Energy (translateFunction shift function) =
      finiteGowersU2Energy function := by
  unfold finiteGowersU2Energy
  apply Finset.sum_congr rfl
  intro direction _
  rw [directionalCorrelation_translate]

/-- The derivative of a unitary additive character is its directional phase. -/
theorem multiplicativeDerivative_character
    (character : FiniteUnitaryAdditiveCharacter (G := G))
    (direction point : G) :
    multiplicativeDerivative character.value direction point =
      character.value direction := by
  change
    character.value (point + direction) * star (character.value point) =
      character.value direction
  rw [character.map_add]
  calc
    (character.value point * character.value direction) *
        star (character.value point) =
      (character.value point * star (character.value point)) *
        character.value direction := by ring
    _ = character.value direction := by
      rw [character.mul_star]
      simp

/-- Modulation multiplies every derivative by the unit directional phase. -/
theorem multiplicativeDerivative_modulate
    (character : FiniteUnitaryAdditiveCharacter (G := G))
    (function : G → ℂ) (direction point : G) :
    multiplicativeDerivative (modulateFunction character function)
        direction point =
      character.value direction *
        multiplicativeDerivative function direction point := by
  change
    (character.value (point + direction) * function (point + direction)) *
        star (character.value point * function point) =
      character.value direction *
        (function (point + direction) * star (function point))
  rw [map_mul, character.map_add]
  calc
    (character.value point * character.value direction *
          function (point + direction)) *
        (star (function point) * star (character.value point)) =
      (character.value point * star (character.value point)) *
        character.value direction *
          (function (point + direction) * star (function point)) := by ring
    _ = character.value direction *
          (function (point + direction) * star (function point)) := by
      rw [character.mul_star]
      ring

/-- Directional correlation under modulation acquires only the corresponding
unit character phase. -/
theorem directionalCorrelation_modulate
    (character : FiniteUnitaryAdditiveCharacter (G := G))
    (function : G → ℂ) (direction : G) :
    (∑ point,
        multiplicativeDerivative (modulateFunction character function)
          direction point) =
      character.value direction *
        ∑ point, multiplicativeDerivative function direction point := by
  simp_rw [multiplicativeDerivative_modulate]
  exact Finset.sum_mul _ _

/-- Finite `U^2` derivative energy is invariant under modulation by a unitary
additive character. -/
theorem finiteGowersU2Energy_modulate
    (character : FiniteUnitaryAdditiveCharacter (G := G))
    (function : G → ℂ) :
    finiteGowersU2Energy (modulateFunction character function) =
      finiteGowersU2Energy function := by
  unfold finiteGowersU2Energy
  apply Finset.sum_congr rfl
  intro direction _
  rw [directionalCorrelation_modulate, norm_mul,
    character.norm_one, one_mul]

/-- Every unitary additive character has the same finite `U^2` energy as the
constant unit function. -/
theorem finiteGowersU2Energy_character_eq_one
    (character : FiniteUnitaryAdditiveCharacter (G := G)) :
    finiteGowersU2Energy character.value =
      finiteGowersU2Energy (fun _ => 1) := by
  simpa [modulateFunction] using
    finiteGowersU2Energy_modulate character (fun _ => 1)

example : FiniteUnitaryAdditiveCharacter (G := ZMod 1) where
  value := fun _ => 1
  map_zero := rfl
  map_add := by simp
  norm_one := by simp
  mul_star := by simp

#print axioms multiplicativeDerivative_translate
#print axioms directionalCorrelation_translate
#print axioms finiteGowersU2Energy_translate
#print axioms multiplicativeDerivative_character
#print axioms multiplicativeDerivative_modulate
#print axioms finiteGowersU2Energy_modulate
#print axioms finiteGowersU2Energy_character_eq_one

end

end D5.S3.Arithmetic.HigherOrderFourier.GowersTranslationModulationInvariance
