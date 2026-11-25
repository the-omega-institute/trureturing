/- GID: D5/S3/Fourier/Concentration/LatticeConvolutionVariance
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/LatticeConvolutionVariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A variance minorant of the score gives a lattice collision integral. -/

import D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
import D5.S3.Fourier.Concentration.CyclicCollisionCertificate
import D5.S3.Fourier.Concentration.DegreeTwoMomentWitness

/-! The score variance minorant and exact collision averaging over an affine lattice period. -/

open Finset MeasureTheory
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase norm_phase)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow
open D5.S3.Fourier.Concentration.FiniteSincCollisionMoment
open D5.S3.Fourier.Concentration.CyclicCollisionCertificate (latticeFrequency)
open D5.S3.Fourier.Concentration.DegreeTwoMomentWitness (int_near_eq)

noncomputable section

namespace D5.S3.Fourier.Concentration.LatticeConvolutionVariance

/-- A variance budget controls the score norm at every real time. -/
theorem score_variance_lower {J : Type*} [Fintype J] (g w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (a V t : ℝ) (hm : ∑ j, w j * (g j - a)^2 ≤ V * ∑ j, w j) :
    let W := ∑ j, w j
    let margin := fun u : ℝ => max 0 (1 - u/2)
    W * margin (V*t^2) ≤ ‖complexScore g w t‖ := by
  intro W margin
  let x := fun j => g j - a
  have hrot : complexScore g w t = phase a t * complexScore x w t := by
    unfold complexScore
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    calc
      (w j : ℂ) * phase (g j) t = (w j : ℂ) * (phase a t * phase (x j) t) := by
        rw [← character_add]
        congr 2
        dsimp [x]
        ring
      _ = _ := by ring
  have hnorm : ‖complexScore g w t‖ = ‖complexScore x w t‖ := by
    rw [hrot, norm_mul, norm_phase, one_mul]
  rw [hnorm]
  have hbound : W * (1 - V*t^2/2) ≤ (complexScore x w t).re := by
    calc
      _ ≤ ∑ j, w j * (1 - (x j*t)^2/2) := by
        have heq : (∑ j, w j * (1 - (x j*t)^2/2)) =
            W - (∑ j, w j * (x j)^2)*t^2/2 := by
          calc
            _ = ∑ j, (w j - (w j * (x j)^2)*t^2/2) := by
              apply sum_congr rfl
              intro j _
              ring
            _ = _ := by rw [sum_sub_distrib, ← sum_div, ← sum_mul]
        rw [heq]
        have hh := mul_le_mul_of_nonneg_right hm (sq_nonneg t)
        dsimp [x, W]
        linarith
      _ ≤ ∑ j, w j * Real.cos (x j*t) := by
        exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          Real.one_sub_sq_div_two_le_cos (hw j)
      _ = _ := by simp [complexScore, Complex.mul_re, phase_re]
  dsimp [margin]
  by_cases h : 0 ≤ 1 - V*t^2/2
  · rw [max_eq_right h]
    exact hbound.trans (Complex.re_le_norm _)
  · rw [max_eq_left (le_of_not_ge h), mul_zero]
    exact norm_nonneg _

private theorem affine_frequency {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (b h : ℝ) {p : ℕ} {m : J → ℕ} (hm : m ∈ piAntidiag univ p) :
    monomialFrequency (fun j => b+h*(a j : ℝ)) m =
      (p : ℝ)*b+h*(latticeFrequency a m : ℝ) := by
  have hp : ∑ j, (m j : ℝ) = p := by exact_mod_cast (mem_piAntidiag.mp hm).1
  unfold monomialFrequency latticeFrequency
  push_cast
  simp_rw [mul_add, mul_left_comm (m _ : ℝ) h, ← mul_assoc]
  simp_rw [mul_assoc h]
  rw [sum_add_distrib, ← sum_mul, ← mul_sum, hp]

/-- On an affine lattice the full score-period mean equals the sub-step collision mass. -/
theorem lattice_period_collision {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (b h : ℝ) (hh : 0 < h) (w : J → ℝ) (p : ℕ)
    (η : ℝ) (hη : 0 ≤ η) (hηh : η < h) :
    let g := fun j => b+h*(a j : ℝ)
    let period := fun d : ℝ => Real.pi/d
    let A := period h
    intervalMean A (fun t => ‖complexScore g w t‖^(2*p)) =
      tailCollisionMass g w p η := by
  intro g period A
  let s := piAntidiag (univ : Finset J) p
  let x := monomialFrequency g
  let c := monomialWeight w
  have hA : 0 < A := div_pos Real.pi_pos hh
  have hscore : (fun t => ‖complexScore g w t‖^(2*p)) = pairCosineScore s x c :=
    funext (moment_eq_pair g w p)
  rw [hscore]
  unfold pairCosineScore tailCollisionMass nearCollisionMass
  change intervalMean A (fun t => ∑ m ∈ s, ∑ n ∈ s,
    c m*c n*Real.cos ((x m-x n)*t)) =
      ∑ m ∈ s, ∑ n ∈ s, if |x m-x n| ≤ η then c m*c n else 0
  rw [intervalMean_sum A s _ (fun m _ => continuous_finsetSum _ (fun n _ => by fun_prop))]
  apply sum_congr rfl
  intro m hm
  rw [intervalMean_sum A s _ (fun n _ => by fun_prop)]
  apply sum_congr rfl
  intro n hn
  have hdiff : x m - x n = h * ((latticeFrequency a m - latticeFrequency a n : ℤ) : ℝ) := by
    dsimp [x, g]
    rw [affine_frequency a b h hm, affine_frequency a b h hn]
    push_cast
    ring
  let d : ℤ := latticeFrequency a m - latticeFrequency a n
  change x m-x n = h*(d : ℝ) at hdiff
  rw [show (fun t : ℝ => c m*c n*Real.cos ((x m-x n)*t)) =
      fun t => (c m*c n)*Real.cos ((x m-x n)*(0+t)) by simp]
  have hmean (v : ℝ) :
      intervalMean A (fun t => (c m*c n)*Real.cos (v*(0+t))) =
        (c m*c n)*Real.sinc (A*v) := by
    have hj := intervalMean_cos hA v 0
    simp only [mul_zero, Real.cos_zero, one_mul] at hj
    unfold intervalMean at hj ⊢
    rw [intervalIntegral.integral_const_mul]
    rw [smul_eq_mul] at hj
    rw [smul_eq_mul, ← hj]
    ring
  rw [hmean, hdiff]
  have hscale : A*(h*(d : ℝ)) = Real.pi*(d : ℝ) := by
    dsimp [A, period]
    field_simp
  rw [hscale, abs_mul, abs_of_pos hh]
  have hgap : h*|(d : ℝ)| ≤ η ↔ d = 0 := by
    rw [mul_comm h, ← le_div_iff₀ hh]
    have hre : |(d : ℝ) - (0 : ℤ)| ≤ η/h ↔ d = (0 : ℤ) :=
      int_near_eq d 0 (div_nonneg hη hh.le) ((div_lt_one hh).mpr hηh)
    simpa using hre
  simp only [hgap]
  by_cases hd : d = 0
  · simp [hd]
  · have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hdR), mul_comm Real.pi,
      Real.sin_int_mul_pi, zero_div, mul_zero, ite_eq_right hd]

/-- The lattice convolution collision mass retains the integrated variance minorant. -/
theorem lattice_collision_variance_lower {J : Type*} [Fintype J] [DecidableEq J]
    (a : J → ℤ) (b h : ℝ) (hh : 0 < h) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (center V : ℝ) (p : ℕ) (η : ℝ) (hη : 0 ≤ η)
    (hm : ∑ j, w j * ((b + h * (a j : ℝ)) - center)^2 ≤ V * ∑ j, w j) :
    let g := fun j => b+h*(a j : ℝ)
    let W := ∑ j, w j
    let A := Real.pi/h
    let margin := fun u : ℝ => max 0 (1-u/2)
    W^(2*p)*intervalMean A (fun t => (margin (V*t^2))^(2*p)) ≤
      tailCollisionMass g w p η := by
  intro g W A margin
  dsimp [margin]
  have hA : 0 < A := div_pos Real.pi_pos hh
  have hpoint (t : ℝ) : W^(2*p)*(max 0 (1-V*t^2/2))^(2*p) ≤
      ‖complexScore g w t‖^(2*p) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (sum_nonneg fun j _ => hw j) (le_max_left _ _))
      (score_variance_lower g w hw center V t hm) _
  have hcont : Continuous (fun t : ℝ => ‖complexScore g w t‖^(2*p)) :=
    (complexScore_continuous g w).norm.pow _
  have hcont' : Continuous (fun t : ℝ => W^(2*p)*(max 0 (1-V*t^2/2))^(2*p)) := by
    fun_prop
  have hmean : W^(2*p)*intervalMean A (fun t => (max 0 (1-V*t^2/2))^(2*p)) ≤
      intervalMean A (fun t => ‖complexScore g w t‖^(2*p)) := by
    unfold intervalMean
    simp only [smul_eq_mul]
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    apply intervalIntegral.integral_mono_on (by linarith) (hcont'.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
    exact fun t _ => hpoint t
  rw [lattice_period_collision a b h hh w p 0 le_rfl hh] at hmean
  apply hmean.trans
  unfold tailCollisionMass nearCollisionMass
  apply sum_le_sum
  intro m hm'
  apply sum_le_sum
  intro n hn'
  change (if |monomialFrequency g m - monomialFrequency g n| ≤ 0 then
    monomialWeight w m * monomialWeight w n else 0) ≤
    (if |monomialFrequency g m - monomialFrequency g n| ≤ η then
    monomialWeight w m * monomialWeight w n else 0)
  by_cases hzero : |monomialFrequency g m - monomialFrequency g n| ≤ 0
  · rw [ite_eq_left hzero, ite_eq_left (hzero.trans hη)]
  · simp only [hzero, ite_false]
    split_ifs
    · exact mul_nonneg (monomialWeight_nonneg w hw m) (monomialWeight_nonneg w hw n)
    · exact le_rfl

#print axioms score_variance_lower
#print axioms lattice_period_collision
#print axioms lattice_collision_variance_lower

end D5.S3.Fourier.Concentration.LatticeConvolutionVariance
