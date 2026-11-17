/- GID: D5/S3/Analytic/Polynomial/A192205RootLimit
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/A192205RootLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Complete absolute coefficient root limit for OEIS A192205. -/

import D5.S3.Constants.Moments.CountableHankelNegativeWitness
import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! The original integer coefficient sum and its full natural-index root limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Polynomial Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.Polynomial.A192205RootLimit

/-- The original integer polynomial. -/
def p : ℤ[X] := 1 - X - X^2 + X^3

/-- All coefficients through degree 3n, including n = 0. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.range (3*n+1), ((p^n).coeff i).natAbs

private def pc : ℂ[X] := 1 - X - X^2 + X^3
private def radius : ℝ := 16*Real.sqrt 3/9

private theorem circle_bound_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1-z-z^2+z^3‖^2 ≤ (256/27 : ℝ) := by
  have hzsq : z.re^2+z.im^2=1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa [Complex.normSq_apply, pow_two] using h
  have hm : ‖1-z‖^2=2-2*z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith
  have hp : ‖1+z‖^2=2+2*z.re := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    nlinarith
  have hx : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
  have hid : ‖1-z-z^2+z^3‖^2 = 8*(1-z.re)^2*(1+z.re) := by
    rw [show 1-z-z^2+z^3=(1-z)^2*(1+z) by ring, norm_mul, norm_pow]
    calc
      (‖1-z‖^2*‖1+z‖)^2 = (‖1-z‖^2)^2*‖1+z‖^2 := by ring
      _ = _ := by rw [hm,hp]; ring
  rw [hid]
  have hpos : 0 ≤ (3*z.re+1)^2*(5-3*z.re) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

private theorem circle_attainment : ∃ z : ℂ, ‖z‖ = 1 ∧
    ‖1-z-z^2+z^3‖ = 16*Real.sqrt 3/9 := by
  let z : ℂ := ⟨-1/3, 2*Real.sqrt 2/3⟩
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hz : ‖z‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z]
    nlinarith
  refine ⟨z,hz,?_⟩
  have hm : ‖1-z‖^2 = 8/3 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    dsimp [z]
    nlinarith
  have hp : ‖1+z‖^2 = 4/3 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    dsimp [z]
    nlinarith
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity : (0:ℝ) ≤ 16*Real.sqrt 3/9)).mp
  rw [show 1-z-z^2+z^3=(1-z)^2*(1+z) by ring, norm_mul, norm_pow]
  calc
    (‖1-z‖^2*‖1+z‖)^2 = (‖1-z‖^2)^2*‖1+z‖^2 := by ring
    _ = _ := by rw [hm,hp]; nlinarith

private theorem coefficient_sum (n : ℕ) :
    (a n : ℝ) =
    ∑ i ∈ ((1-X-X^2+X^3 : ℂ[X])^n).support,
      ‖((1-X-X^2+X^3 : ℂ[X])^n).coeff i‖ := by
  unfold a p
  have hmap : (((1-X-X^2+X^3 : ℤ[X])^n).map (Int.castRingHom ℂ)) =
      (1-X-X^2+X^3 : ℂ[X])^n := by simp
  have hdegree : ((1-X-X^2+X^3 : ℂ[X])^n).natDegree ≤ 3*n := by
    rw [Polynomial.natDegree_pow]
    have hp : (1-X-X^2+X^3 : ℂ[X]).natDegree ≤ 3 := by compute_degree
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right n hp
  calc
    _ = ∑ i ∈ Finset.range (3*n+1), ‖((1-X-X^2+X^3 : ℂ[X])^n).coeff i‖ := by
      simp only [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [←hmap]
      simp only [Polynomial.coeff_map, Int.castRingHom]
      simp [Nat.cast_natAbs, Int.cast_abs]
    _ = _ := by
      symm
      exact ((1-X-X^2+X^3 : ℂ[X])^n).sum_over_range'
        (fun _ => by simp) (3*n+1) (by omega)

theorem power_sum_sq_le (p : ℂ[X]) (M : ℝ)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) (n : ℕ) :
    (∑ i ∈ (p^n).support, ‖(p^n).coeff i‖)^2 ≤
      ((p^n).support.card : ℝ) * M^(2*n) := by
  have hparseval : ∑ i ∈ (p^n).support, ‖(p^n).coeff i‖^2 ≤ M^(2*n) := by
    rw [(p^n).sum_sq_norm_coeff_eq_circleAverage]
    apply Real.circleAverage_mono_on_of_le_circle
      (((p^n).continuous.norm.pow 2).continuousOn.circleIntegrable (by norm_num))
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    simp only [Polynomial.eval_pow, norm_pow]
    calc
      (‖p.eval z‖^n)^2 ≤ (M^n)^2 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hM z hz1) n) 2
      _ = _ := by ring
  calc
    (∑ i ∈ (p^n).support, ‖(p^n).coeff i‖)^2 ≤
      ((p^n).support.card : ℝ) * ∑ i ∈ (p^n).support, ‖(p^n).coeff i‖^2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq (p^n).support (fun _ => (1:ℝ))
          (fun i => ‖(p^n).coeff i‖)
    _ ≤ _ := mul_le_mul_of_nonneg_left hparseval (Nat.cast_nonneg _)

private theorem lower_bound (n : ℕ) : radius^n ≤ (a n : ℝ) := by
  obtain ⟨z, hz, hmax⟩ := circle_attainment
  let pr : ℝ[X] := (p^n).map (Int.castRingHom ℝ)
  have heval := D5.S3.Constants.Moments.CountableHankelNegativeWitness.eval_bound pr hz.le
  have heq : pr.eval₂ Complex.ofRealHom z = (1-z-z^2+z^3)^n := by
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
    have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    have he : pc.eval z = 1-z-z^2+z^3 := by simp [pc]
    rw [he]
    apply (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ radius from hM)).mp
    dsimp [radius]
    nlinarith
  have hs := power_sum_sq_le pc radius hcircle n
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

theorem degree_root_limit : Tendsto (fun n : ℕ => (3*(n:ℝ)+1)^(1/(n:ℝ))) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => 3*(n:ℝ)+1) atTop atTop := by
    exact Tendsto.atTop_add
      (Tendsto.const_mul_atTop (by norm_num : (0:ℝ) < 3) tendsto_natCast_atTop_atTop)
      tendsto_const_nhds
  have h := (tendsto_rpow_div_mul_add 3 1 (-1) (by norm_num)).comp hn
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp
  congr 1
  field_simp
  ring


/-- Hanna's complete absolute-coefficient root-limit conjecture. -/
theorem result : Tendsto (fun n : ℕ => (a n : ℝ) ^ (1/(n:ℝ)))
    atTop (𝓝 (16*Real.sqrt 3/9)) := by
  have hM : 0 ≤ radius := by unfold radius; positivity
  have hupper : Tendsto (fun n : ℕ => (3*(n:ℝ)+1)^(1/(n:ℝ))*radius)
      atTop (𝓝 radius) := by
    simpa using degree_root_limit.mul_const radius
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

end D5.S3.Analytic.Polynomial.A192205RootLimit
