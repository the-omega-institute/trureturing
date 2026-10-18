/- GID: D5/S3/Zeros/CriticalPoints/SchurStripFunctions
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/SchurStripFunctions
   mirror-E: none(waiver:general-complex-interpolation)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Hadamard]
   utility: none
   digest: Entire matrix functions used by the scalar Schur interpolation argument. -/

import D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
import D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Explicit interpolation functions and their analytic strip data. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.SchurStripFunctions

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers ThreeLinesSchurMoment

def F (n : ℕ) (u : Fin n → ℂ) (t : Fin n → ℝ) (p : ℝ) (ζ : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  H n ((p : ℂ) * ζ / 2) * diagonal (fun j => u j * positivePower (t j) ((p : ℂ) * ζ)) *
    H n ((p : ℂ) * ζ / 2)

def K (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (ρ : Fin n → ℝ) (p : ℝ) (ζ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Q * diagonal (fun k => conj (v k) * positivePower (ρ k) ((p : ℂ) * (1 - ζ))) * Qᴴ

def f (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ)
    (t ρ : Fin n → ℝ) (p : ℝ) (ζ : ℂ) : ℂ :=
  trace (K n Q v ρ p ζ * F n u t p ζ)

private theorem positive_power_strip (x a : ℝ) (b : ℂ) :
    StripData (fun ζ : ℂ => positivePower x (ζ * (a : ℂ) + b)) := by
  convert StripData.exp_real_slope (a * Real.log x) (b * (Real.log x : ℂ)) using 1
  funext ζ
  unfold positivePower
  congr 1
  push_cast
  ring

private theorem H_strip (n : ℕ) (a : ℝ) (b : ℂ) (i j : Fin n) :
    StripData (fun ζ : ℂ => H n (ζ * (a : ℂ) + b) i j) := by
  simpa only [H_apply, div_eq_mul_inv, sub_eq_add_neg] using
    (StripData.const (if i = j then (1 : ℂ) else 0)).add
      (((positive_power_strip ((n : ℝ) + 1) a b).add (StripData.const (-1))).mul
        (StripData.const ((n : ℂ)⁻¹)))

private theorem matrix_mul_strip {n : ℕ}
    {A B : ℂ → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ i j, StripData (fun ζ => A ζ i j))
    (hB : ∀ i j, StripData (fun ζ => B ζ i j)) (i j : Fin n) :
    StripData (fun ζ => (A ζ * B ζ) i j) := by
  exact StripData.sum Finset.univ (fun k ζ => A ζ i k * B ζ k j)
    (fun k _ => (hA i k).mul (hB k j))

private theorem F_strip (n : ℕ) (u : Fin n → ℂ) (t : Fin n → ℝ) (p : ℝ)
    (i j : Fin n) : StripData (fun ζ => F n u t p ζ i j) := by
  have hH : ∀ i j : Fin n, StripData (fun ζ => H n ((p : ℂ) * ζ / 2) i j) := by
    intro i j
    convert H_strip n (p / 2) 0 i j using 1
    funext ζ
    congr 2
    push_cast
    ring
  have hD : ∀ i j : Fin n, StripData (fun ζ =>
      diagonal (fun k => u k * positivePower (t k) ((p : ℂ) * ζ)) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      convert (StripData.const (u i)).mul (positive_power_strip (t i) p 0) using 1
      funext ζ
      simp only [add_zero, mul_comm]
    · simp only [diagonal_apply_ne _ hij]
      exact StripData.const 0
  exact matrix_mul_strip (fun i j => matrix_mul_strip hH hD i j) hH i j

private theorem K_strip (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ)
    (ρ : Fin n → ℝ) (p : ℝ) (i j : Fin n) :
    StripData (fun ζ => K n Q v ρ p ζ i j) := by
  have hD : ∀ i j : Fin n, StripData (fun ζ =>
      diagonal (fun k => conj (v k) * positivePower (ρ k) ((p : ℂ) * (1 - ζ))) i j) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      convert (StripData.const (conj (v i))).mul
        (positive_power_strip (ρ i) (-p) (p : ℂ)) using 1
      funext ζ
      congr 2
      push_cast
      ring
    · simp only [diagonal_apply_ne _ hij]
      exact StripData.const 0
  exact matrix_mul_strip
    (fun i j => matrix_mul_strip (fun a b => StripData.const (Q a b)) hD i j)
    (fun a b => StripData.const (Qᴴ a b)) i j

theorem f_strip (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ)
    (t ρ : Fin n → ℝ) (p : ℝ) : StripData (f n Q u v t ρ p) := by
  exact StripData.sum Finset.univ
    (fun i ζ => (K n Q v ρ p ζ * F n u t p ζ) i i)
    (fun i _ => matrix_mul_strip (K_strip n Q v ρ p) (F_strip n u t p) i i)

private theorem diagonal_unitary (n : ℕ) (d : Fin n → ℂ) (hd : ∀ i, ‖d i‖ = 1) :
    diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change diagonal d * (diagonal d)ᴴ = 1
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_eq_one]
  funext i
  change d i * conj (d i) = 1
  rw [Complex.mul_conj', hd]
  norm_num

private theorem F_unitary_left (n : ℕ) (hn : 0 < n) (u : Fin n → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (t : Fin n → ℝ) (p y : ℝ) :
    F n u t p ((y : ℂ) * I) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hH : H n ((p : ℂ) * ((y : ℂ) * I) / 2) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have he : (p : ℂ) * ((y : ℂ) * I) / 2 = ((p * y / 2 : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [he]
    exact H_unitary n hn _
  have hD := diagonal_unitary n
    (fun i => u i * positivePower (t i) ((p : ℂ) * ((y : ℂ) * I))) (by
      intro i
      rw [norm_mul, hu, one_mul, norm_positivePower]
      simp [Complex.mul_re])
  exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hH hD) hH

theorem K_unitary_right (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : Fin n → ℂ)
    (hv : ∀ i, ‖v i‖ = 1) (ρ : Fin n → ℝ) (p y : ℝ) :
    K n Q v ρ p (1 + (y : ℂ) * I) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hD := diagonal_unitary n
    (fun i => conj (v i) * positivePower (ρ i) ((p : ℂ) * (1 - (1 + (y : ℂ) * I)))) (by
      intro i
      rw [norm_mul, Complex.norm_conj, hv, one_mul, norm_positivePower]
      simp [Complex.mul_re])
  have hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hQ
  exact (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hQ hD) hQs

private theorem unitary_diag_norm_le_one (n : ℕ) (V : Matrix (Fin n) (Fin n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) : ‖V i i‖ ≤ 1 := by
  have hVV : V * Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hV
  have hs := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => (A i i).re) hVV
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.re_sum, Complex.ofReal_re, Matrix.one_apply_eq,
    Complex.one_re] at hs
  have hle := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
    sq_nonneg ‖V i k‖) (Finset.mem_univ i)
  rw [hs] at hle
  nlinarith [norm_nonneg (V i i)]

theorem left_bound (n : ℕ) (hn : 0 < n) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (u v : Fin n → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (t ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) (p : ℝ)
    (hmass : ∑ i, ρ i ^ p = 1) (y : ℝ) :
    ‖f n Q u v t ρ p ((y : ℂ) * I)‖ ≤ 1 := by
  let V := Qᴴ * F n u t p ((y : ℂ) * I) * Q
  let d : Fin n → ℂ := fun i =>
    conj (v i) * positivePower (ρ i) ((p : ℂ) * (1 - (y : ℂ) * I))
  have hQs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa only [Matrix.star_eq_conjTranspose] using Unitary.star_mem hQ
  have hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (Matrix.unitaryGroup (Fin n) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hQs (F_unitary_left n hn u hu t p y)) hQ
  have hd (i : Fin n) : ‖d i‖ = ρ i ^ p := by
    dsimp only [d]
    rw [norm_mul, Complex.norm_conj, hv, one_mul, norm_positivePower,
      Real.rpow_def_of_pos (hρ i)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.sub_re, Complex.one_re, sub_zero, Complex.I_re,
      Complex.I_im, mul_one]
    congr 1
    ring
  have htrace : f n Q u v t ρ p ((y : ℂ) * I) = trace (diagonal d * V) := by
    unfold f K
    change trace ((Q * diagonal d * Qᴴ) * F n u t p ((y : ℂ) * I)) = _
    rw [show (Q * diagonal d * Qᴴ) * F n u t p ((y : ℂ) * I) =
      Q * (diagonal d * (Qᴴ * F n u t p ((y : ℂ) * I))) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [V, Matrix.mul_assoc]
  rw [htrace, Matrix.trace]
  calc
    ‖∑ i, (diagonal d * V) i i‖ ≤ ∑ i, ‖(diagonal d * V) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ρ i ^ p := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Matrix.diagonal_mul, norm_mul, hd]
      exact (mul_le_mul_of_nonneg_left (unitary_diag_norm_le_one n V hV i)
        (Real.rpow_nonneg (hρ i).le p)).trans_eq (mul_one _)
    _ = 1 := hmass

end D5.S3.Zeros.CriticalPoints.SchurStripFunctions
