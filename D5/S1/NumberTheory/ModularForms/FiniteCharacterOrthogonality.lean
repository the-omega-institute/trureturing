/- GID: D5/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality
   generality: G
   mirror-B: D5/B/S1/NumberTheory/ModularForms/FiniteCharacterOrthogonality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-group character orthogonality and unitary norm-square mass.
-/

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

namespace D5.S1.NumberTheory.ModularForms

open scoped BigOperators

/-!
This is the finite-character orthogonality input used by Gauss-sum and
Hasse--Davenport arguments.  It is proved here without an analytic Hecke
operator or a supplied character-sum estimate: the only ingredient is the
translation permutation of a finite group.  Consequently this file is a
genuine algebraic bridge, not a conditional interface for the missing
analytic modular-form action.
-/

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

/-- A nontrivial multiplicative character has vanishing total sum. -/
theorem nontrivial_character_sum_eq_zero (χ : G →* ℂ) (hχ : χ ≠ 1) :
    ∑ g : G, χ g = 0 := by
  classical
  have h_exists : ∃ a : G, χ a ≠ (1 : ℂ) := by
    by_contra h
    push Not at h
    apply hχ
    ext g
    simpa using h g
  obtain ⟨a, ha⟩ := h_exists
  let S : ℂ := ∑ g : G, χ g
  have htranslate : χ a * S = S := by
    dsimp [S]
    calc
      χ a * ∑ g : G, χ g = ∑ g : G, χ a * χ g := by
        rw [Finset.mul_sum]
      _ = ∑ g : G, χ (a * g) := by
        simp_rw [map_mul]
      _ = ∑ g : G, χ g := by
        exact Fintype.sum_equiv (Equiv.mulLeft a)
          (fun g : G => χ (a * g)) (fun g : G => χ g) (fun _ => rfl)
  have hzero : (χ a - 1) * S = 0 := by
    rw [sub_mul, htranslate, one_mul, sub_self]
  have hdiff : χ a - 1 ≠ 0 := sub_ne_zero.mpr ha
  have : S = 0 := (mul_eq_zero.mp hzero).resolve_left hdiff
  exact this

/-- The square norm mass of a unitary multiplicative character is the group order.

The unit-modulus hypothesis is explicit because a monoid hom into `ℂ` need not
land in the unit circle.  This is the exact normalization consumed by the
usual Gauss-sum norm calculation. -/
theorem unitary_character_norm_sq_sum_eq_card
    (χ : G →* ℂ) (hunit : ∀ g : G, ‖χ g‖ = 1) :
    ∑ g : G, ‖χ g‖ ^ 2 = Fintype.card G := by
  classical
  simp [hunit]

end

end D5.S1.NumberTheory.ModularForms

#print axioms D5.S1.NumberTheory.ModularForms.nontrivial_character_sum_eq_zero
#print axioms D5.S1.NumberTheory.ModularForms.unitary_character_norm_sq_sum_eq_card
