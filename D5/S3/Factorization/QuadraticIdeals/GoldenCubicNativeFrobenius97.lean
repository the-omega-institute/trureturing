/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeFrobenius97
   mirror-E: none(waiver:exact-native-prime-witness)
   anchors: []
   utility: none
   digest: Actual good-reduction point counts and five independent Frobenius squareclasses at 97. -/

import D5.S3.Factorization.QuadraticIdeals.FiniteLegendreSquareclassCertificate
import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFiveProbes
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Matrix

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFrobenius97

open D5.S3.Factorization.QuadraticIdeals.FiniteLegendreSquareclassCertificate
open D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFiveProbes
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic

private def auxiliary : Fin 5 → ℕ := ![5,7,13,19,29]

local instance auxPrime : ∀ i : Fin 5, Fact (auxiliary i).Prime := fun i =>
  ⟨(by decide : ∀ i : Fin 5, (auxiliary i).Prime) i⟩

/-- Frobenius discriminants supplied by the first five native traces at 97. -/
def at97 : Fin 5 → ℤ := ![-288,-379,-363,-307,-384]

/-- The observed prime 97 is a quadratic nonresidue at every auxiliary row. -/
theorem at97_auxiliary_nonsquare (i : Fin 5) : legendreSym (auxiliary i) 97 = -1 := by
  fin_cases i <;> decide

private def at97Matrix : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1,0,1,1,0; 1,1,0,0,0; 1,1,0,1,1; 0,0,0,0,1; 1,1,1,1,0]

private def at97Inverse : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1,1,0,0,1; 1,0,0,0,1; 0,0,1,1,1; 0,1,1,1,0; 0,0,0,1,0]

set_option maxRecDepth 4096 in
private theorem at97Matrix_eq : legendreMatrix auxiliary at97 = at97Matrix := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> decide

private theorem at97Inverse_mul : at97Inverse * at97Matrix = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> decide

/-- None of the 31 nonempty products of the five explicit at-97 discriminants is a rational square. -/
private theorem at97_not_isSquare_product (s : Finset (Fin 5)) (hs : s.Nonempty) :
    ¬IsSquare (∏ j ∈ s, (at97 j : ℚ)) := by
  apply not_isSquare_product_of_injective auxiliary at97 _ _ s hs
  · decide
  · rw [at97Matrix_eq]
    exact injective_mulVec_of_left_inverse _ _ at97Inverse_mul

local instance prime97 : Fact (Nat.Prime 97) := ⟨by decide⟩

private def residue97 : Fin 5 → ZMod 97 := ![4,76,85,79,31]
def counts97 : Fin 5 → ℕ := ![88,101,103,107,100]

private theorem residue_eq (i : Fin 5) : (goldenLucas (3^(i.val+1)) : ZMod 97) = residue97 i := by
  have h1 : (goldenLucas (3 ^ 1) : ZMod 97) = 4 := by decide
  have h2 : (goldenLucas (3 ^ 2) : ZMod 97) = 76 := by
    rw [show (2 : ℕ) = 1 + 1 by decide, orbit_step 1 (by decide), h1]
    decide
  have h3 : (goldenLucas (3 ^ 3) : ZMod 97) = 85 := by
    rw [show (3 : ℕ) = 2 + 1 by decide, orbit_step 2 (by decide), h2]
    decide
  have h4 : (goldenLucas (3 ^ 4) : ZMod 97) = 79 := by
    rw [show (4 : ℕ) = 3 + 1 by decide, orbit_step 3 (by decide), h3]
    decide
  have h5 : (goldenLucas (3 ^ 5) : ZMod 97) = 31 := by
    rw [show (5 : ℕ) = 4 + 1 by decide, orbit_step 4 (by decide), h4]
    decide
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

private def rootMass97 (a : ZMod 97) : ℕ :=
  if a.val = 0 then 1 else if a.val^48 % 97 = 1 then 2 else 0

private theorem fiber_card97 (a : ZMod 97) :
    Fintype.card {y : ZMod 97 // y^2 = a} = rootMass97 a := by
  rw [Fintype.card_subtype]
  have hc : ringChar (ZMod 97) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have H := quadraticChar_card_sqrts hc a
  rw [Set.toFinset_ofPred] at H
  unfold rootMass97
  simp only [ZMod.val_eq_zero]
  have hcast : a^48 = ((a.val^48 : ℕ) : ZMod 97) := by
    rw [Nat.cast_pow, ZMod.natCast_zmod_val]
  have hval : (a^48).val = a.val^48 % 97 := by rw [hcast, ZMod.val_natCast]
  have hone : a.val^48 % 97 = 1 ↔ a^48 = 1 := by
    simp only [← hval]
    exact ⟨fun h => ZMod.val_injective 97 (h.trans (by decide : (1 : ZMod 97).val = 1).symm),
      fun h => congrArg ZMod.val h |>.trans (by decide)⟩
  simp only [hone]
  by_cases ha : a = 0
  · simp only [ha, ite_true]
    rw [ha, quadraticChar_zero, zero_add] at H
    exact_mod_cast H
  · rw [quadraticChar_eq_pow_of_char_ne_two hc ha, ZMod.card] at H
    by_cases hb : a^48 = 1
    · simp only [ha, hb, ite_true, ite_false]
      have h' : a^(97/2) = 1 := hb
      simp [h'] at H
      exact_mod_cast H
    · simp only [ha, hb, ite_false]
      have h' : a^(97/2) ≠ 1 := hb
      simp [h'] at H
      simpa using H

private def fiberEquiv97 (l : ZMod 97) :
    {z : ZMod 97 × ZMod 97 // z.2^2 = equation l z.1} ≃
      (Σ x : ZMod 97, {y : ZMod 97 // y^2 = equation l x}) where
  toFun z := ⟨z.1.1, z.1.2, z.2⟩
  invFun z := ⟨(z.1,z.2.1), z.2.2⟩
  left_inv := by rintro ⟨⟨x,y⟩,h⟩; rfl
  right_inv := by rintro ⟨x,y,h⟩; rfl

private theorem count_fast97 (l : ZMod 97) :
    count 97 l = 1 + ∑ x : ZMod 97, rootMass97 (equation l x) := by
  unfold count
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberEquiv97 l), Fintype.card_sigma]
  simp only [fiber_card97]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 700000 in
private theorem exact_counts (i : Fin 5) : count 97 (residue97 i) = counts97 i := by
  rw [count_fast97]
  fin_cases i <;> decide

private theorem good97 (i : Fin 5) : (model (residue97 i) 1).Δ ≠ 0 := by
  rw [model_discriminant]
  fin_cases i <;> decide

/-- Good reduction and the actual point count at every one of the first five levels. -/
theorem native_at97_good_count (i : Fin 5) :
    let l := (goldenLucas (3^(i.val+1)) : ZMod 97)
    (model l 1).Δ ≠ 0 ∧ Nat.card (model l 1).Point = counts97 i := by
  dsimp only
  rw [residue_eq i]
  exact ⟨good97 i, (card_curve_points 97 _ (good97 i)).trans (exact_counts i)⟩

/-- At 97 these are the discriminants of actual native finite-field point counts. -/
noncomputable def nativeDiscriminant97 (i : Fin 5) : ℤ :=
  (98 - (Nat.card (model (goldenLucas (3^(i.val+1)) : ZMod 97) 1).Point : ℤ)) ^ 2 - 388

theorem nativeDiscriminant97_eq (i : Fin 5) : nativeDiscriminant97 i = at97 i := by
  unfold nativeDiscriminant97
  rw [(native_at97_good_count i).2]
  fin_cases i <;> decide

/-- The five actual Frobenius discriminants at 97 have no rational squareclass relation. -/
theorem native_at97_not_isSquare_product (s : Finset (Fin 5)) (hs : s.Nonempty) :
    ¬IsSquare (∏ j ∈ s, (nativeDiscriminant97 j : ℚ)) := by
  simpa only [nativeDiscriminant97_eq] using at97_not_isSquare_product s hs

#print axioms native_at97_not_isSquare_product

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeFrobenius97
