/- GID: D5/S3/Analytic/Polynomial/A195417RootLimit
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/A195417RootLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complete absolute coefficient root limit for OEIS A195417. -/

import D5.S3.Analytic.Polynomial.A192205RootLimit
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The original integer coefficient sum and its full natural-index root limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.Polynomial.A195417RootLimit

/-- The original integer polynomial. -/
def p : ℤ[X] := 1 + X - X^3

/-- All coefficients through degree 3n, including n = 0. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (3*n+1), ((p^n).coeff i).natAbs

private def pc : ℂ[X] := 1 + X - X^3
private def radius : ℝ := Real.sqrt ((97+26*Real.sqrt 13)/27)

private theorem circle_norm_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1+z-z^3‖^2 = 5+8*z.re-4*z.re^2-8*z.re^3 := by
  have hzsq : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa [Complex.normSq_apply, pow_two] using h
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_succ, pow_zero, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.one_im, Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  linear_combination
    (z.re^4-z.re^2+6*z.re+z.im^4+z.im^2*(2*z.re^2+3)+4) * hzsq

private theorem circle_bound_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1+z-z^3‖^2 ≤ (97+26*Real.sqrt 13)/27 := by
  rw [circle_norm_sq z hz]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 13 by norm_num)
  have hs0 := Real.sqrt_nonneg (13:ℝ)
  have hsbound : (5:ℝ)/2 ≤ Real.sqrt 13 := by nlinarith
  have hx : -1 ≤ z.re := by
    have h := Complex.abs_re_le_norm z
    rw [hz] at h
    exact (abs_le.mp h).1
  have hgap : (97+26*Real.sqrt 13)/27 - (5+8*z.re-4*z.re^2-8*z.re^3) =
      (6*z.re+1-Real.sqrt 13)^2*(6*z.re+1+2*Real.sqrt 13)/27 := by
    linear_combination ((-2*Real.sqrt 13+18*z.re+3)/27) * hs
  have hpos : 0 ≤ (6*z.re+1-Real.sqrt 13)^2*(6*z.re+1+2*Real.sqrt 13)/27 :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by norm_num)
  linarith

private theorem circle_attainment : ∃ z : ℂ, ‖z‖ = 1 ∧
    ‖1+z-z^3‖ = Real.sqrt ((97+26*Real.sqrt 13)/27) := by
  let u : ℝ := (-1+Real.sqrt 13)/6
  let z : ℂ := ⟨u, Real.sqrt (1-u^2)⟩
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 13 by norm_num)
  have hs0 := Real.sqrt_nonneg (13:ℝ)
  have hule : u ≤ 1 := by dsimp [u]; nlinarith
  have huge : -1 ≤ u := by dsimp [u]; nlinarith
  have hu : 0 ≤ 1-u^2 := by nlinarith
  have hv := Real.sq_sqrt hu
  have hz : ‖z‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    nlinarith
  refine ⟨z,hz,?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [circle_norm_sq z hz, Real.sq_sqrt (by positivity)]
  dsimp [z,u]
  linear_combination (-Real.sqrt 13/27) * hs

private theorem coefficient_sum (n : ℕ) :
    (a n : ℝ) =
    ∑ i ∈ ((1+X-X^3 : ℂ[X])^n).support,
      ‖((1+X-X^3 : ℂ[X])^n).coeff i‖ := by
  unfold a p
  have hmap : (((1+X-X^3 : ℤ[X])^n).map (Int.castRingHom ℂ)) =
      (1+X-X^3 : ℂ[X])^n := by simp
  have hdegree : ((1+X-X^3 : ℂ[X])^n).natDegree ≤ 3*n := by
    rw [Polynomial.natDegree_pow]
    have hp : (1+X-X^3 : ℂ[X]).natDegree ≤ 3 := by compute_degree
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp
  calc
    _ = ∑ i ∈ Finset.range (3*n+1), ‖((1+X-X^3 : ℂ[X])^n).coeff i‖ := by
      simp only [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [←hmap]
      simp only [Polynomial.coeff_map, Int.castRingHom]
      simp [Nat.cast_natAbs, Int.cast_abs]
    _ = _ := by
      symm
      exact ((1+X-X^3 : ℂ[X])^n).sum_over_range'
        (fun _ => by simp) (3*n+1) (by omega)

private theorem lower_bound (n : ℕ) : radius^n ≤ (a n : ℝ) := by
  obtain ⟨z, hz, hmax⟩ := circle_attainment
  let pr : ℝ[X] := (p^n).map (Int.castRingHom ℝ)
  have heval := D5.S3.Constants.Moments.CountableHankelNegativeWitness.eval_bound pr hz.le
  have heq : pr.eval₂ Complex.ofRealHom z = (1+z-z^3)^n := by
    simp [pr, p, Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_sub]
  have hdegree : pr.natDegree ≤ 3*n := by
    dsimp [pr]
    apply (Polynomial.natDegree_map_le).trans
    rw [Polynomial.natDegree_pow]
    have hp : p.natDegree ≤ 3 := by unfold p; compute_degree
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp
  have hsum : ∑ i ∈ pr.support, |pr.coeff i| = (a n : ℝ) := by
    change pr.sum (fun _ c => |c|) = _
    rw [pr.sum_over_range' (fun _ => by simp) (3*n+1) (by omega)]
    simp only [a, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [pr, Polynomial.coeff_map, Int.castRingHom]
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [heq, norm_pow, hmax, hsum] at heval
  exact heval

private theorem upper_bound (n : ℕ) : (a n : ℝ) ≤ (3*(n:ℝ)+1)*radius^n := by
  have hM : 0 ≤ radius := by unfold radius; positivity
  have hcircle : ∀ z : ℂ, ‖z‖ = 1 → ‖pc.eval z‖ ≤ radius := by
    intro z hz
    have hb := circle_bound_sq z hz
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ (97+26*Real.sqrt 13)/27 by positivity)
    have he : pc.eval z = 1+z-z^3 := by simp [pc]
    rw [he]
    apply (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ radius from hM)).mp
    dsimp [radius]
    nlinarith
  have hs := D5.S3.Analytic.Polynomial.A192205RootLimit.power_sum_sq_le pc radius hcircle n
  have hd : (pc^n).natDegree ≤ 3*n := by
    rw [Polynomial.natDegree_pow]
    have hp : pc.natDegree ≤ 3 := by unfold pc; compute_degree
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp
  have hcard : (pc^n).support.card ≤ 3*n+1 := by
    calc
      (pc^n).support.card ≤ (Finset.range (3*n+1)).card :=
        Finset.card_le_card (Polynomial.supp_subset_range (by omega))
      _ = 3*n+1 := Finset.card_range _
  have hcast : ((pc^n).support.card : ℝ) ≤ 3*(n:ℝ)+1 := by exact_mod_cast hcard
  have hsum : (a n : ℝ) = ∑ i ∈ (pc^n).support, ‖(pc^n).coeff i‖ := coefficient_sum n
  rw [←hsum] at hs
  have hs' : (a n : ℝ)^2 ≤ (3*(n:ℝ)+1) * (radius^n)^2 := by
    calc
      (a n : ℝ)^2 ≤ ((pc^n).support.card : ℝ) * radius^(2*n) := hs
      _ ≤ (3*(n:ℝ)+1)*radius^(2*n) := mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = _ := by ring
  have hk : (1:ℝ) ≤ 3*(n:ℝ)+1 := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hp : 0 ≤ radius^n := pow_nonneg hM n
  have hsq : (a n : ℝ)^2 ≤ ((3*(n:ℝ)+1)*radius^n)^2 := by
    have hmul : (0:ℝ) ≤ (3*(n:ℝ)+1-1)*((3*(n:ℝ)+1)*(radius^n)^2) :=
      mul_nonneg (sub_nonneg.mpr hk)
        (mul_nonneg (show (0:ℝ) ≤ 3*(n:ℝ)+1 by positivity) (sq_nonneg (radius^n)))
    nlinarith
  exact (sq_le_sq₀ (Nat.cast_nonneg _) (mul_nonneg (by positivity) hp)).mp hsq

/-- The complete first root-limit question in OEIS A195417. -/
theorem result : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1/(n:ℝ)))
    atTop (𝓝 (Real.sqrt ((97+26*Real.sqrt 13)/27))) := by
  have hM : 0 ≤ radius := by unfold radius; positivity
  have hupper : Tendsto (fun n : ℕ => (3*(n:ℝ)+1)^(1/(n:ℝ))*radius)
      atTop (𝓝 radius) := by
    simpa using D5.S3.Analytic.Polynomial.A192205RootLimit.degree_root_limit.mul_const radius
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    have hroot : (radius^n : ℝ)^(1/(n:ℝ)) = radius := by
      simpa [one_div] using Real.pow_rpow_inv_natCast hM hn0
    rw [← hroot]
    exact Real.rpow_le_rpow (pow_nonneg hM n) (lower_bound n) (by positivity)
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn0 : n ≠ 0 := by omega
    have hroot : (radius^n : ℝ)^(1/(n:ℝ)) = radius := by
      simpa [one_div] using Real.pow_rpow_inv_natCast hM hn0
    calc
      (a n : ℝ)^(1/(n:ℝ)) ≤ ((3*(n:ℝ)+1)*radius^n)^(1/(n:ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (upper_bound n) (by positivity)
      _ = (3*(n:ℝ)+1)^(1/(n:ℝ))*radius := by
        rw [Real.mul_rpow (by positivity) (pow_nonneg hM n), hroot]

end D5.S3.Analytic.Polynomial.A195417RootLimit
