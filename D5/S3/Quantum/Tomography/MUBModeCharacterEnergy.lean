/- GID: D5/S3/Quantum/Tomography/MUBModeCharacterEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBModeCharacterEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three-mode collision above the uniform baseline is exactly the squared order-three character coordinate. -/

import D5.S3.Quantum.Tomography.MUBModeAffinitySharpBound

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBModeCharacterEnergy

open D5.S3.Quantum.Tomography.MUBModeSymmetryBudget

/-- The squared norm of the nontrivial order-three character coordinate of a
real triple, written without adjoining a complex cube root. -/
def threeModeCharacterSquare (p : Fin 3 → ℝ) : ℝ :=
  (p 0 - (p 1 + p 2) / 2) ^ 2 +
    (3 / 4 : ℝ) * (p 1 - p 2) ^ 2

/-- The character square is the collision after removing the trivial
all-one character. This identity does not require normalization or
nonnegativity. -/
theorem threeModeCharacterSquare_eq_collision_removed_trivial
    (p : Fin 3 → ℝ) :
    threeModeCharacterSquare p =
      (3 * threeModeCollision p - (p 0 + p 1 + p 2) ^ 2) / 2 := by
  unfold threeModeCharacterSquare threeModeCollision
  ring

/-- On the probability hyperplane, the order-three character square is
`(3 collision - 1) / 2`. -/
theorem threeModeCharacterSquare_eq_of_sum_one
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    threeModeCharacterSquare p =
      (3 * threeModeCollision p - 1) / 2 := by
  rw [threeModeCharacterSquare_eq_collision_removed_trivial]
  rw [hsum]
  ring

/-- The proposed single-vector collision threshold `2 / 3` is exactly the
character-energy threshold `1 / 2`. -/
theorem two_thirds_le_collision_iff_half_le_characterSquare
    (p : Fin 3 → ℝ)
    (hsum : p 0 + p 1 + p 2 = 1) :
    (2 / 3 : ℝ) ≤ threeModeCollision p ↔
      (1 / 2 : ℝ) ≤ threeModeCharacterSquare p := by
  rw [threeModeCharacterSquare_eq_of_sum_one p hsum]
  constructor <;> intro h <;> linarith

/-- Uniform mode weights have zero nontrivial character energy. -/
theorem threeModeCharacterSquare_uniform :
    threeModeCharacterSquare
      ![(1 / 3 : ℝ), (1 / 3 : ℝ), (1 / 3 : ℝ)] = 0 := by
  norm_num [threeModeCharacterSquare]

/-- A mode-local probability vector has maximal character square one. -/
theorem threeModeCharacterSquare_modeLocal :
    threeModeCharacterSquare ![(1 : ℝ), 0, 0] = 1 := by
  norm_num [threeModeCharacterSquare]

/-- Character square is always nonnegative. -/
theorem threeModeCharacterSquare_nonneg (p : Fin 3 → ℝ) :
    0 ≤ threeModeCharacterSquare p := by
  unfold threeModeCharacterSquare
  positivity

#print axioms threeModeCharacterSquare_eq_collision_removed_trivial
#print axioms threeModeCharacterSquare_eq_of_sum_one
#print axioms two_thirds_le_collision_iff_half_le_characterSquare
#print axioms threeModeCharacterSquare_uniform
#print axioms threeModeCharacterSquare_modeLocal
#print axioms threeModeCharacterSquare_nonneg

end D5.S3.Quantum.Tomography.MUBModeCharacterEnergy
