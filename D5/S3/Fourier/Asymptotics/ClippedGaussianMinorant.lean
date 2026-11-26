/- GID: D5/S3/Fourier/Asymptotics/ClippedGaussianMinorant
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/ClippedGaussianMinorant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clipped power integrals approximate Gaussian mass uniformly in the window. -/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The clipped cosine minorant converges after the natural variance rescaling. -/

open MeasureTheory Filter Set
open scoped Topology Interval

noncomputable section

namespace D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant

private def profile (n : ℕ) (u : ℝ) : ℝ :=
  (max 0 (1-u^2/(2*(n : ℝ))))^(2*n)

private def gaussian (u : ℝ) : ℝ := Real.exp (-u^2)

private theorem gaussian_integrable : Integrable gaussian := by
  unfold gaussian
  simpa using (integrable_exp_neg_mul_sq (b := 1) zero_lt_one)

private theorem gaussian_integral : (∫ u : ℝ, gaussian u) = Real.sqrt Real.pi := by
  simpa [gaussian] using integral_gaussian 1

private theorem profile_nonneg (n : ℕ) (u : ℝ) : 0 ≤ profile n u := by
  exact pow_nonneg (le_max_left _ _) _

private theorem profile_le {n : ℕ} (hn : 0 < n) (u : ℝ) :
    profile n u ≤ gaussian u := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : max 0 (1-u^2/(2*(n : ℝ))) ≤ Real.exp (-(u^2/(2*(n : ℝ)))) :=
    max_le (Real.exp_pos _).le (Real.one_sub_le_exp_neg _)
  unfold profile gaussian
  calc
    _ ≤ (Real.exp (-(u^2/(2*(n : ℝ)))))^(2*n) :=
      pow_le_pow_left₀ (le_max_left _ _) hbase _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp

private theorem profile_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => profile n u) atTop (𝓝 (gaussian u)) := by
  have h := (Real.tendsto_one_add_div_pow_exp (-(u^2)/2)).pow 2
  have hlim : Real.exp (-(u^2)/2)^2 = gaussian u := by
    rw [← Real.exp_nat_mul]
    unfold gaussian
    congr 1
    norm_num
    ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (u^2/2)] with n hn hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hn)
  unfold profile
  rw [max_eq_right (by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    linarith)]
  rw [mul_comm 2 n, pow_mul]
  congr 2
  field_simp <;> ring

private theorem profile_continuous (n : ℕ) : Continuous (profile n) := by
  unfold profile
  fun_prop

private theorem profile_integrable {n : ℕ} (hn : 0 < n) : Integrable (profile n) := by
  apply gaussian_integrable.mono' (profile_continuous n).aestronglyMeasurable
  exact ae_of_all _ fun u => by rw [Real.norm_of_nonneg (profile_nonneg n u)]; exact profile_le hn u

private theorem profile_error_tendsto :
    Tendsto (fun n : ℕ => ∫ u : ℝ, |profile n u-gaussian u|) atTop (𝓝 0) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun n u => |profile n u-gaussian u|) (f := fun _ : ℝ => (0:ℝ))
    gaussian
    (Eventually.of_forall fun n => by
      apply Continuous.aestronglyMeasurable
      unfold profile gaussian
      fun_prop)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      exact ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_abs, abs_of_nonpos (sub_nonpos.mpr (profile_le hn u))]
        linarith [profile_nonneg n u])
    gaussian_integrable
    (ae_of_all _ fun u => by
      simpa using ((profile_tendsto u).sub (tendsto_const_nhds (x := gaussian u))).abs)
  simpa using hlim

private theorem window_error {n : ℕ} (hn : 0 < n) (r : ℝ) :
    |(∫ u in -r..r, profile n u) - (∫ u in -r..r, gaussian u)| ≤
      ∫ u : ℝ, |profile n u-gaussian u| := by
  have h₁ := (profile_integrable hn).intervalIntegrable (a := -r) (b := r)
  have h₂ := gaussian_integrable.intervalIntegrable (a := -r) (b := r)
  rw [← intervalIntegral.integral_sub h₁ h₂]
  calc
    _ ≤ ∫ u in Ι (-r) r, ‖profile n u-gaussian u‖ := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := fun u => profile n u-gaussian u)
          (a := -r) (b := r))
    _ ≤ _ := by
      simp_rw [Real.norm_eq_abs]
      exact setIntegral_le_integral ((profile_integrable hn).sub gaussian_integrable).abs
        (ae_of_all _ fun _ => abs_nonneg _)

/-- After the variance scaling, the integral error tends to zero for arbitrary oriented windows. -/
theorem clipped_gaussian_window_error (V A : ℕ → ℝ) (hV : ∀ᶠ n in atTop, 0 < V n) :
    let scale := fun n : ℕ => Real.sqrt ((n : ℝ)*V n)
    let R := fun n => A n*scale n
    let readout := fun u : ℝ => Real.exp (-u^2)
    Tendsto (fun n => scale n *
      (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n)) -
      ∫ u in -(R n)..R n, readout u) atTop (𝓝 0) := by
  intro scale R readout
  have hscale (n : ℕ) (hn : 0 < n) (hv : 0 < V n) :
      scale n * (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n)) =
        ∫ u in -(R n)..R n, profile n u := by
    have hspos : 0 < scale n := Real.sqrt_pos.mpr (by positivity)
    have hs : scale n ^ 2 = (n : ℝ)*V n := Real.sq_sqrt (by positivity)
    have heq : (fun t : ℝ => (max 0 (1-V n*t^2/2))^(2*n)) =
        fun t => profile n (scale n*t) := by
      funext t
      unfold profile
      congr 2
      rw [mul_pow, hs]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [heq]
    have h := intervalIntegral.smul_integral_comp_mul_left (f := profile n)
      (a := -(A n)) (b := A n) (c := scale n)
    simpa only [smul_eq_mul, mul_neg, R, mul_comm (scale n) (A n)] using h
  have hneg : Tendsto (fun n : ℕ => -(∫ u : ℝ, |profile n u-gaussian u|)) atTop (𝓝 0) := by
    simpa only [neg_zero] using profile_error_tendsto.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg profile_error_tendsto
  · filter_upwards [eventually_ge_atTop (1 : ℕ), hV] with n hn hv
    rw [hscale n hn hv]
    exact (abs_le.mp (window_error hn (R n))).1
  · filter_upwards [eventually_ge_atTop (1 : ℕ), hV] with n hn hv
    rw [hscale n hn hv]
    exact (abs_le.mp (window_error hn (R n))).2

private theorem gaussian_window_mono : Monotone (fun r : ℝ => ∫ u in -r..r, gaussian u) := by
  intro r s hrs
  have h₁ := gaussian_integrable.intervalIntegrable (a := -s) (b := -r)
  have h₂ := gaussian_integrable.intervalIntegrable (a := -r) (b := r)
  have h₃ := gaussian_integrable.intervalIntegrable (a := r) (b := s)
  have he := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  have he' := intervalIntegral.integral_add_adjacent_intervals (h₁.trans h₂) h₃
  have hp₁ : 0 ≤ ∫ u in -s..-r, gaussian u :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => Real.exp_nonneg _)
  have hp₃ : 0 ≤ ∫ u in r..s, gaussian u :=
    intervalIntegral.integral_nonneg hrs (fun u _ => Real.exp_nonneg _)
  linarith

private theorem gaussian_window_lt (r : ℝ) :
    (∫ u in -r..r, gaussian u) < Real.sqrt Real.pi := by
  let s := max r 1
  have hmono := gaussian_window_mono (le_max_left r 1)
  have hs : 0 < s := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hp : 0 < ∫ u in s..s+1, gaussian u :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      (gaussian_integrable.intervalIntegrable (a := s) (b := s+1)) (fun _ _ => Real.exp_pos _) (by linarith)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (gaussian_integrable.intervalIntegrable (a := -s) (b := s))
    (gaussian_integrable.intervalIntegrable (a := s) (b := s+1))
  have hle : (∫ u in -s..s+1, gaussian u) ≤ Real.sqrt Real.pi := by
    rw [intervalIntegral.integral_of_le (by linarith), ← gaussian_integral]
    exact setIntegral_le_integral gaussian_integrable (ae_of_all _ fun _ => Real.exp_nonneg _)
  linarith

/-- The full Gaussian limit is equivalent to divergence of the rescaled oriented half-width. -/
theorem clipped_gaussian_full_limit_iff (V A : ℕ → ℝ) (hV : ∀ᶠ n in atTop, 0 < V n) :
    let scale := fun n : ℕ => Real.sqrt ((n : ℝ)*V n)
    let R := fun n => A n*scale n
    let readout := fun u : ℝ => Real.exp (-u^2)
    Tendsto (fun n => scale n *
      (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n))) atTop
      (𝓝 (∫ u : ℝ, readout u)) ↔ Tendsto R atTop atTop := by
  intro scale R readout
  let I := fun n : ℕ => scale n *
    (∫ t in -(A n)..A n, (max 0 (1-V n*t^2/2))^(2*n))
  let G := fun n : ℕ => ∫ u in -(R n)..R n, gaussian u
  have herror : Tendsto (fun n => I n - G n) atTop (𝓝 0) :=
    clipped_gaussian_window_error V A hV
  change Tendsto I atTop (𝓝 (∫ u : ℝ, gaussian u)) ↔ _
  rw [gaussian_integral]
  constructor
  · intro hI
    have hG : Tendsto G atTop (𝓝 (Real.sqrt Real.pi)) := by
      simpa only [sub_zero, sub_sub_cancel] using hI.sub herror
    rw [tendsto_atTop]
    intro r
    filter_upwards [hG.eventually_const_lt (gaussian_window_lt r)] with n hn
    by_contra! hnr
    exact (not_lt_of_ge (gaussian_window_mono hnr.le)) hn
  · intro hR
    have hG : Tendsto G atTop (𝓝 (Real.sqrt Real.pi)) := by
      rw [← gaussian_integral]
      exact intervalIntegral_tendsto_integral gaussian_integrable (tendsto_neg_atTop_atBot.comp hR) hR
    simpa only [zero_add, sub_add_cancel] using herror.add hG

#print axioms clipped_gaussian_window_error
#print axioms clipped_gaussian_full_limit_iff

end D5.S3.Fourier.Asymptotics.ClippedGaussianMinorant
