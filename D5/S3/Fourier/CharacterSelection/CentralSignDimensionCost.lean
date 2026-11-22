/- GID: D5/S3/Fourier/CharacterSelection/CentralSignDimensionCost
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/CentralSignDimensionCost
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separating k central bits costs at least 4k+1 squared dimensions, with rigid equality. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost

/-- A separating binary profile on a k-dimensional cube has constant readings in its
one-dimensional channels and m further binary readings, of integer dimensions at least two.
Including a distinguished trivial channel costs at least 4k+1. Equality forces the precise
support shape and makes the m remaining readings bijective on the cube. -/
theorem central_sign_dimension_cost {k r m : ℕ} (d : Fin m → ℕ)
    (profile : (Fin k → Bool) → (Fin r → Bool) × (Fin m → Bool))
    (hsep : Function.Injective profile)
    (hconst : ∀ x y, (profile x).1 = (profile y).1)
    (hd : ∀ j, 2 ≤ d j) :
    k ≤ m ∧ 4 * k + 1 ≤ 1 + r + ∑ j, d j ^ 2 ∧
      ((1 + r + ∑ j, d j ^ 2) = 4 * k + 1 ↔
        m = k ∧ r = 0 ∧ (∀ j, d j = 2) ∧ Function.Bijective (fun x => (profile x).2)) := by
  classical
  have hinj : Function.Injective (fun x => (profile x).2) := by
    intro x y h
    exact hsep (Prod.ext (hconst x y) h)
  have hp : (2 : ℕ) ^ k ≤ 2 ^ m := by
    simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  have hkm : k ≤ m := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hp
  have hfour (j : Fin m) : 4 ≤ d j ^ 2 := by nlinarith [hd j]
  have hsum : 4 * m ≤ ∑ j, d j ^ 2 := by
    simpa [Nat.mul_comm] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hfour j))
  refine ⟨hkm, by omega, ?_⟩
  constructor
  · intro heq
    have hm : m = k := by omega
    refine ⟨hm, by omega, ?_, ?_⟩
    · intro j
      by_contra hj
      have hj' : 4 < d j ^ 2 := by
        have : 2 < d j := by have := hd j; omega
        nlinarith
      have hlt := Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hfour i)
        ⟨j, Finset.mem_univ _, hj'⟩
      have : 4 * m < ∑ i, d i ^ 2 := by simpa [Nat.mul_comm] using hlt
      omega
    · subst m
      exact hinj.bijective_of_finite
  · rintro ⟨rfl, rfl, hd', _⟩
    simp [hd', Nat.mul_comm, Nat.add_comm]

#print axioms central_sign_dimension_cost

end D5.S3.Fourier.CharacterSelection.CentralSignDimensionCost
