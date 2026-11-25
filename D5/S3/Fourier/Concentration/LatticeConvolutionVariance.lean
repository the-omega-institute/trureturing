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
    (a V t : ℝ) (hm : ∑ j, w j * (g j - a) ^ 2 ≤ V * ∑ j, w j) :
    let W := ∑ j, w j
    let margin := fun u : ℝ => max 0 (1 - u/2)
    let B := ∑ j, w j * (g j-a)^2
    W * margin (V*t^2) ≤ ‖complexScore g w t‖ ∧
    max 0 (W-B*t^2/2) ≤ ‖complexScore g w t‖ ∧
    (0 < B → t ≠ 0 → W-B*t^2/2 < ‖complexScore g w t‖) := by
  intro W margin B
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
  have heq : (∑ j, w j * (1 - (x j*t)^2/2)) = W-B*t^2/2 := by
    calc
      _ = ∑ j, (w j - (w j * (x j)^2)*t^2/2) := by
        apply sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [sum_sub_distrib, ← sum_div, ← sum_mul]
  have hre : (complexScore x w t).re = ∑ j, w j * Real.cos (x j*t) := by
    simp [complexScore, Complex.mul_re, phase_re]
  have hbound : W-B*t^2/2 ≤ (complexScore x w t).re := by
    rw [← heq, hre]
    exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      Real.one_sub_sq_div_two_le_cos (hw j)
  have hbudget : W * (1-V*t^2/2) ≤ W-B*t^2/2 := by
    have hh := mul_le_mul_of_nonneg_right hm (sq_nonneg t)
    change B * t^2 ≤ V * W * t^2 at hh
    linarith
  have hn := Complex.re_le_norm (complexScore x w t)
  refine ⟨?_, max_le (norm_nonneg _) (hbound.trans hn), ?_⟩
  · dsimp [margin]
    by_cases h : 0 ≤ 1 - V*t^2/2
    · rw [max_eq_right h]
      exact hbudget.trans (hbound.trans hn)
    · rw [max_eq_left (le_of_not_ge h), mul_zero]
      exact norm_nonneg _
  · intro hB ht
    have hwx : ∃ j, 0 < w j * (x j)^2 := by
      by_contra! hall
      have hz : B ≤ 0 := sum_nonpos fun j _ => hall j
      linarith
    obtain ⟨j, hj⟩ := hwx
    have hwj : 0 < w j := by
      by_contra! h
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg _))) hj
    have hxj : x j ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hj
      exact (lt_irrefl _ hj)
    rw [← heq, hre] at hbound
    have hstrict : W-B*t^2/2 < (complexScore x w t).re := by
      rw [← heq, hre]
      apply sum_lt_sum
      · exact fun i _ => mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos (hw i)
      · exact ⟨j, mem_univ _, mul_lt_mul_of_pos_left
          (Real.one_sub_sq_div_two_lt_cos (mul_ne_zero hxj ht)) hwj⟩
    exact hstrict.trans_le hn

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
    (η : ℝ) (hη : 0 ≤ η) (hηh : η < h) (k : ℕ) (hk : 0 < k) (s₀ : ℝ) :
    let g := fun j => b+h*(a j : ℝ)
    let period := fun d : ℝ => Real.pi/d
    let A := (k : ℝ)*period h
    intervalMean A (fun t => ‖complexScore g w (s₀+t)‖^(2*p)) =
      tailCollisionMass g w p η := by
  intro g period A
  let s := piAntidiag (univ : Finset J) p
  let x := monomialFrequency g
  let c := monomialWeight w
  have hA : 0 < A := mul_pos (by exact_mod_cast hk) (div_pos Real.pi_pos hh)
  have hscore : (fun t => ‖complexScore g w (s₀+t)‖^(2*p)) =
      (fun t => pairCosineScore s x c (s₀+t)) :=
    funext fun t => moment_eq_pair g w p (s₀+t)
  rw [hscore]
  unfold pairCosineScore tailCollisionMass nearCollisionMass
  change intervalMean A (fun t => ∑ m ∈ s, ∑ n ∈ s,
    c m*c n*Real.cos ((x m-x n)*(s₀+t))) =
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
  have hmean (v : ℝ) :
      intervalMean A (fun t => (c m*c n)*Real.cos (v*(s₀+t))) =
        (c m*c n)*Real.cos (v*s₀)*Real.sinc (A*v) := by
    calc
      _ = (c m*c n)*intervalMean A (fun t => Real.cos (v*(s₀+t))) := by
        unfold intervalMean
        rw [intervalIntegral.integral_const_mul]
        simp only [smul_eq_mul]
        ring
      _ = _ := by rw [intervalMean_cos hA v s₀]; ring
  rw [hmean, hdiff]
  have hscale : A*(h*(d : ℝ)) = Real.pi*((k : ℤ)*d : ℤ) := by
    dsimp [A, period]
    push_cast
    field_simp
    <;> ring
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
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hdK : (((k : ℤ)*d : ℤ) : ℝ) ≠ 0 := by
      push_cast
      exact mul_ne_zero hkR hdR
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hdK), mul_comm Real.pi,
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
    let B := ∑ j, w j * (g j-center)^2
    W^(2*p)*intervalMean A (fun t => (margin (V*t^2))^(2*p)) ≤
      tailCollisionMass g w p η ∧
    (0 < B → 0 < p →
      W^(2*p)*intervalMean A (fun t => (margin (V*t^2))^(2*p)) <
        tailCollisionMass g w p η) := by
  intro g W A margin B
  dsimp [margin]
  have hA : 0 < A := div_pos Real.pi_pos hh
  have hpoint (t : ℝ) : W^(2*p)*(max 0 (1-V*t^2/2))^(2*p) ≤
      ‖complexScore g w t‖^(2*p) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (sum_nonneg fun j _ => hw j) (le_max_left _ _))
      (score_variance_lower g w hw center V t hm).1 _
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
  have hperiod : intervalMean A (fun t => ‖complexScore g w t‖^(2*p)) =
      tailCollisionMass g w p 0 := by
    simpa only [Nat.cast_one, one_mul, zero_add] using
      lattice_period_collision a b h hh w p 0 le_rfl hh 1 (by decide) 0
  rw [hperiod] at hmean
  have hmono : tailCollisionMass g w p 0 ≤ tailCollisionMass g w p η := by
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
  refine ⟨hmean.trans hmono, ?_⟩
  intro hB hp
  have hW0 : 0 ≤ W := sum_nonneg fun j _ => hw j
  have hVW : 0 < V*W := hB.trans_le hm
  have hV : 0 < V := by
    by_contra! hV
    exact not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hV hW0) hVW
  let t := min (A/2) (1/(1+V))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htA : t ≤ A := (min_le_left _ _).trans (by linarith)
  have htone : t ≤ 1 := (min_le_right _ _).trans
    ((div_le_one (by positivity)).mpr (by linarith))
  have htv : V*t ≤ 1 := by
    have hl := min_le_right (A/2) (1/(1+V))
    have hl' := (le_div_iff₀ (by positivity : 0 < 1+V)).mp hl
    nlinarith
  have hsmall : 0 ≤ 1-V*t^2/2 := by
    have hh := mul_le_mul_of_nonneg_right htv ht.le
    nlinarith
  have hstrict : W * (max 0 (1-V*t^2/2)) < ‖complexScore g w t‖ := by
    rw [max_eq_right hsmall]
    have h := (score_variance_lower g w hw center V t hm).2.2 hB ht.ne'
    have hmul := mul_le_mul_of_nonneg_right hm (sq_nonneg t)
    change B*t^2 ≤ V*W*t^2 at hmul
    have hbudget : W*(1-V*t^2/2) ≤ W-B*t^2/2 := by linarith
    exact hbudget.trans_lt h
  have hstrict_pow : W^(2*p)*(max 0 (1-V*t^2/2))^(2*p) <
      ‖complexScore g w t‖^(2*p) := by
    rw [← mul_pow]
    exact pow_lt_pow_left₀ hstrict (mul_nonneg hW0 (le_max_left _ _)) (by omega)
  have hmeanStrict : W^(2*p)*intervalMean A (fun t => (max 0 (1-V*t^2/2))^(2*p)) <
      intervalMean A (fun t => ‖complexScore g w t‖^(2*p)) := by
    unfold intervalMean
    simp only [smul_eq_mul]
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    apply mul_lt_mul_of_pos_left _ (inv_pos.mpr (by positivity))
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by linarith) hcont'.continuousOn hcont.continuousOn (fun t _ => hpoint t)
    exact ⟨t, ⟨by linarith, htA⟩, hstrict_pow⟩
  rw [hperiod] at hmeanStrict
  exact hmeanStrict.trans_le hmono

#print axioms score_variance_lower
#print axioms lattice_period_collision
#print axioms lattice_collision_variance_lower

end D5.S3.Fourier.Concentration.LatticeConvolutionVariance
