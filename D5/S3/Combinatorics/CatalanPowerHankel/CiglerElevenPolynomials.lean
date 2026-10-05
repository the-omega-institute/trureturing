/- GID: D5/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CatalanPowerHankel/CiglerElevenPolynomials
   mirror-E: none(waiver:recurrence-polynomial-identities)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Chebyshev]
   utility: none
   digest: Chebyshev recurrences prove residue identities and construct their monic quotients. -/

import D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenReduction
import Mathlib.RingTheory.Polynomial.Chebyshev

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false

set_option quotPrecheck false

noncomputable section

namespace D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenPolynomials

open Polynomial CiglerElevenMoments

open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelOrthogonal
open D5.S3.Combinatorics.MotzkinHankel.CiglerMotzkinHankelDefs

local notation "P" => (fun n : ℕ => Polynomial.map
  (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i : Fin 2 => if i = 0 then 2 else 1))
  (orthogonal n))

local notation "H" => (fun n : ℕ => Polynomial.map
  (MvPolynomial.eval₂Hom (Int.castRingHom ℚ) (fun i : Fin 2 => if i = 0 then 2 else 3))
  (orthogonal n))

/-- Recurrence identities for the residue-class reduction and its exact monic quotients. -/
theorem polynomial_structure :
    (∀ k j : ℕ, P (2 * k + 1 + j) - P j =
      P k * (Chebyshev.C ℚ ((k + j + 1 : ℕ) : ℤ)).comp (X - 2)) ∧
    (∀ k s : ℕ, s ≤ k → P (k + s) + P (k - s) =
      P k * (Chebyshev.C ℚ (s : ℤ)).comp (X - 2)) ∧
    (∀ B t : ℕ, 0 < B → t < B → P (B + t) + P (B - 1 - t) =
      X * (Chebyshev.S ℚ ((B - 1 : ℕ) : ℤ)).comp (X - 2) * H t) := by
  have Pcheb (n : ℕ) : P n =
      (Chebyshev.S ℚ (n : ℤ) + Chebyshev.S ℚ ((n : ℤ) - 1)).comp (X - 2) := by
    have hrec (a : ℕ) :
        (Chebyshev.S ℚ ((a : ℤ) + 2) + Chebyshev.S ℚ ((a : ℤ) + 1)) =
        X * (Chebyshev.S ℚ ((a : ℤ) + 1) + Chebyshev.S ℚ (a : ℤ)) -
          (Chebyshev.S ℚ (a : ℤ) + Chebyshev.S ℚ ((a : ℤ) - 1)) := by
      have h₁ := Chebyshev.S_add_two ℚ (a : ℤ)
      have h₂ := Chebyshev.S_add_two ℚ ((a : ℤ) - 1)
      rw [show (a : ℤ) - 1 + 2 = (a : ℤ) + 1 by omega] at h₂
      simp only [sub_add_cancel] at h₂
      linear_combination h₁ + h₂
    induction n using Nat.twoStepInduction with
    | zero => simp [orthogonal]
    | one => simp [orthogonal, sVar, Chebyshev.S_one]; ring
    | more a ih₀ ih₁ =>
      have hc := congrArg (fun f : ℚ[X] => f.comp (X - 2)) (hrec a)
      simp only [add_comp, sub_comp, mul_comp, X_comp] at hc
      have step : P (a + 2) = (X - 2) * P (a + 1) - P a := by
        simp [orthogonal, tVar, Polynomial.map_sub, Polynomial.map_mul, Polynomial.C_ofNat]
      rw [step, ih₀, ih₁]
      convert hc.symm using 1 <;>
        simp [show (a : ℤ) + 2 - 1 = (a : ℤ) + 1 by omega]
  have Hcheb (n : ℕ) : H n =
      (Chebyshev.S ℚ (n : ℤ) - Chebyshev.S ℚ ((n : ℤ) - 1)).comp (X - 2) := by
    have hrec (a : ℕ) :
        (Chebyshev.S ℚ ((a : ℤ) + 2) - Chebyshev.S ℚ ((a : ℤ) + 1)) =
        X * (Chebyshev.S ℚ ((a : ℤ) + 1) - Chebyshev.S ℚ (a : ℤ)) -
          (Chebyshev.S ℚ (a : ℤ) - Chebyshev.S ℚ ((a : ℤ) - 1)) := by
      have h₁ := Chebyshev.S_add_two ℚ (a : ℤ)
      have h₂ := Chebyshev.S_add_two ℚ ((a : ℤ) - 1)
      rw [show (a : ℤ) - 1 + 2 = (a : ℤ) + 1 by omega] at h₂
      simp only [sub_add_cancel] at h₂
      linear_combination h₁ - h₂
    induction n using Nat.twoStepInduction with
    | zero => simp [orthogonal]
    | one => simp [orthogonal, sVar, Chebyshev.S_one, Polynomial.C_ofNat]; ring
    | more a ih₀ ih₁ =>
      have hc := congrArg (fun f : ℚ[X] => f.comp (X - 2)) (hrec a)
      simp only [sub_comp, mul_comp, X_comp] at hc
      have step : H (a + 2) = (X - 2) * H (a + 1) - H a := by
        simp [orthogonal, tVar, Polynomial.map_sub, Polynomial.map_mul, Polynomial.C_ofNat]
      rw [step, ih₀, ih₁]
      convert hc.symm using 1 <;>
        simp [show (a : ℤ) + 2 - 1 = (a : ℤ) + 1 by omega]
  have product (n : ℤ) (m : ℕ) :
      Chebyshev.C ℚ (m : ℤ) * Chebyshev.S ℚ n =
        Chebyshev.S ℚ (n + m) + Chebyshev.S ℚ (n - m) := by
    induction m using Nat.twoStepInduction with
    | zero => simp; ring
    | one =>
      have hh := Chebyshev.S_add_one ℚ n
      simp only [Nat.cast_one, Chebyshev.C_one]
      linear_combination -hh
    | more m ih₀ ih₁ =>
      have hc := Chebyshev.C_add_two ℚ (m : ℤ)
      have hf := Chebyshev.S_add_two ℚ (n + m)
      have hb := Chebyshev.S_sub_two ℚ (n - m)
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at ih₁ ⊢
      have hi₁ : n + ((m : ℤ) + 1) = n + m + 1 := by omega
      have hi₂ : n - ((m : ℤ) + 1) = n - m - 1 := by omega
      have hi₃ : n + ((m : ℤ) + 2) = n + m + 2 := by omega
      have hi₄ : n - ((m : ℤ) + 2) = n - m - 2 := by omega
      rw [hi₁, hi₂] at ih₁
      rw [hi₃, hi₄]
      linear_combination Chebyshev.S ℚ n * hc + X * ih₁ - ih₀ - hf - hb
  have quotient (t : ℕ) :
      (Chebyshev.C ℚ ((t + 1 : ℕ) : ℤ) + Chebyshev.C ℚ (t : ℤ)).comp (X - 2) =
        X * H t := by
    have hc₁ := Chebyshev.C_eq_S_sub_X_mul_S ℚ ((t : ℤ) + 1)
    have hc₀ := Chebyshev.C_eq_S_sub_X_mul_S ℚ (t : ℤ)
    have hs := Chebyshev.S_add_one ℚ (t : ℤ)
    simp only [add_sub_cancel_right] at hc₁
    have raw : Chebyshev.C ℚ ((t : ℤ) + 1) + Chebyshev.C ℚ (t : ℤ) =
        (X + 2) * (Chebyshev.S ℚ (t : ℤ) - Chebyshev.S ℚ ((t : ℤ) - 1)) := by
      linear_combination hc₁ + hc₀ + 2 * hs
    have hh := congrArg (fun f : ℚ[X] => f.comp (X - 2)) raw
    simpa [add_comp, mul_comp, Hcheb] using hh
  refine ⟨?_, ?_, ?_⟩
  · intro k j
    have hp₁ := product (k : ℤ) (k + j + 1)
    have hp₀ := product ((k : ℤ) - 1) (k + j + 1)
    have hi₁ : (k : ℤ) + (k + j + 1 : ℕ) = (2 * k + 1 + j : ℕ) := by omega
    have hi₂ : (k : ℤ) - (k + j + 1 : ℕ) = -(j : ℤ) - 1 := by omega
    have hi₃ : (k : ℤ) - 1 + (k + j + 1 : ℕ) = (2 * k + 1 + j : ℕ) - 1 := by omega
    have hi₄ : (k : ℤ) - 1 - (k + j + 1 : ℕ) = -(j : ℤ) - 2 := by omega
    rw [hi₁, hi₂, Chebyshev.S_neg_sub_one] at hp₁
    rw [hi₃, hi₄, Chebyshev.S_neg_sub_two] at hp₀
    have hh := congrArg (fun f : ℚ[X] => f.comp (X - 2)) (show
        (Chebyshev.S ℚ ((2 * k + 1 + j : ℕ) : ℤ) +
          Chebyshev.S ℚ (((2 * k + 1 + j : ℕ) : ℤ) - 1)) -
        (Chebyshev.S ℚ (j : ℤ) + Chebyshev.S ℚ ((j : ℤ) - 1)) =
        (Chebyshev.S ℚ (k : ℤ) + Chebyshev.S ℚ ((k : ℤ) - 1)) *
          Chebyshev.C ℚ ((k + j + 1 : ℕ) : ℤ) by linear_combination -hp₁ - hp₀)
    simpa [Pcheb, add_comp, sub_comp, mul_comp] using hh
  · intro k s hs
    have hp₁ := product (k : ℤ) s
    have hp₀ := product ((k : ℤ) - 1) s
    have hi₁ : (k : ℤ) + s = (k + s : ℕ) := by omega
    have hi₂ : (k : ℤ) - s = (k - s : ℕ) := by omega
    have hi₃ : (k : ℤ) - 1 + s = (k + s : ℕ) - 1 := by omega
    have hi₄ : (k : ℤ) - 1 - s = (k - s : ℕ) - 1 := by omega
    rw [hi₁, hi₂] at hp₁
    rw [hi₃, hi₄] at hp₀
    have hh := congrArg (fun f : ℚ[X] => f.comp (X - 2)) (show
        (Chebyshev.S ℚ ((k + s : ℕ) : ℤ) + Chebyshev.S ℚ (((k + s : ℕ) : ℤ) - 1)) +
        (Chebyshev.S ℚ ((k - s : ℕ) : ℤ) + Chebyshev.S ℚ (((k - s : ℕ) : ℤ) - 1)) =
        (Chebyshev.S ℚ (k : ℤ) + Chebyshev.S ℚ ((k : ℤ) - 1)) *
          Chebyshev.C ℚ (s : ℤ) by linear_combination -hp₁ - hp₀)
    simpa [Pcheb, add_comp, mul_comp] using hh
  · intro B t hB ht
    have hp₁ := product ((B - 1 : ℕ) : ℤ) (t + 1)
    have hp₀ := product ((B - 1 : ℕ) : ℤ) t
    have hi₁ : ((B - 1 : ℕ) : ℤ) + (t + 1 : ℕ) = (B + t : ℕ) := by omega
    have hi₂ : ((B - 1 : ℕ) : ℤ) - (t + 1 : ℕ) = (B - 1 - t : ℕ) - 1 := by omega
    have hi₃ : ((B - 1 : ℕ) : ℤ) + t = (B + t : ℕ) - 1 := by omega
    have hi₄ : ((B - 1 : ℕ) : ℤ) - t = (B - 1 - t : ℕ) := by omega
    rw [hi₁, hi₂] at hp₁
    rw [hi₃, hi₄] at hp₀
    have hh := congrArg (fun f : ℚ[X] => f.comp (X - 2)) (show
        (Chebyshev.S ℚ ((B + t : ℕ) : ℤ) + Chebyshev.S ℚ (((B + t : ℕ) : ℤ) - 1)) +
        (Chebyshev.S ℚ ((B - 1 - t : ℕ) : ℤ) +
          Chebyshev.S ℚ (((B - 1 - t : ℕ) : ℤ) - 1)) =
        Chebyshev.S ℚ ((B - 1 : ℕ) : ℤ) *
          (Chebyshev.C ℚ ((t + 1 : ℕ) : ℤ) + Chebyshev.C ℚ (t : ℤ)) by
            linear_combination -hp₁ - hp₀)
    simp only [mul_comp] at hh
    rw [quotient] at hh
    simpa [Pcheb, add_comp, mul_comm, mul_left_comm, mul_assoc] using hh

end D5.S3.Combinatorics.CatalanPowerHankel.CiglerElevenPolynomials
