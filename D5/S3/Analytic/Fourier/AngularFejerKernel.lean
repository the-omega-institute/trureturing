/- GID: D5/S3/Analytic/Fourier/AngularFejerKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Fourier/AngularFejerKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Angular Fejer kernels, their notched variants, and logarithmic averages.
 -/

import D5.S3.TotalVariation.Asymptotics.StatLeanFourierCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped FourierTransform Real Topology BigOperators

namespace D5.S3.Analytic.Fourier.AngularFejerKernel

noncomputable section

noncomputable def K (b v : ℝ) : ℝ := b / (2 * Real.pi) * Real.sinc (b * v / 2) ^ 2

noncomputable def phi (b t : ℝ) : ℝ := max 0 (1 - |t| / b)

noncomputable def H (b U v : ℝ) : ℝ := K b v * (1 - Real.cos (U * v))

noncomputable def psi (b U t : ℝ) : ℝ := phi b t - phi b (t - U) / 2 - phi b (t + U) / 2

/-- angular Fourier transform -/
noncomputable def aft (g : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ v : ℝ, (g v : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ))

noncomputable def ell (u : ℝ) : ℝ := Real.log (Real.exp 1 + u)

open StatLean.HypothesisTesting

private lemma K_nonneg {b : ℝ} (hb : 0 < b) (v : ℝ) : 0 ≤ K b v := by
  unfold K
  positivity

private lemma K_cap {b : ℝ} (hb : 0 < b) (v : ℝ) : K b v ≤ b / (2 * Real.pi) := by
  have hs := Real.abs_sinc_le_one (b * v / 2)
  have hs2 : Real.sinc (b * v / 2) ^ 2 ≤ 1 := by
    rcases abs_le.mp hs with ⟨hlo, hhi⟩
    nlinarith
  unfold K
  nlinarith [div_pos hb (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)]

private lemma K_bound {b : ℝ} (hb : 0 < b) {v : ℝ} (hv : v ≠ 0) :
    K b v ≤ 2 / (Real.pi * b * v ^ 2) := by
  have ha : b * v / 2 ≠ 0 := by positivity
  have he : K b v = 2 * Real.sin (b * v / 2) ^ 2 / (Real.pi * b * v ^ 2) := by
    unfold K
    rw [Real.sinc_of_ne_zero ha]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_right (by nlinarith [Real.sin_sq_le_one (b*v/2)]) (by positivity)

private lemma H_nonneg {b : ℝ} (hb : 0 < b) (U v : ℝ) : 0 ≤ H b U v := by
  exact mul_nonneg (K_nonneg hb v) (sub_nonneg.mpr (Real.cos_le_one _))

private lemma H_le {b : ℝ} (hb : 0 < b) (U v : ℝ) : H b U v ≤ 2 * K b v := by
  unfold H
  nlinarith [Real.neg_one_le_cos (U*v), K_nonneg hb v]

private lemma K_continuous (b : ℝ) : Continuous (K b) := by
  unfold K
  exact continuous_const.mul ((Real.continuous_sinc.comp (by fun_prop)).pow 2)

private lemma H_continuous (b U : ℝ) : Continuous (H b U) := by
  exact (K_continuous b).mul (continuous_const.sub (Real.continuous_cos.comp (by fun_prop)))

private lemma K_tail {b : ℝ} (hb : 0 < b) (hi : Integrable (K b))
    {y : ℝ} (hy : 0 < y) :
    (∫ v in Set.Ici y, K b v) ≤ 2 / (Real.pi * b * y) := by
  rw [integral_Ici_eq_integral_Ioi]
  have hp : IntegrableOn (fun v : ℝ => 2 / (Real.pi * b) * v ^ (-2 : ℝ)) (Ioi y) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hy).const_mul _
  calc
    (∫ v in Ioi y, K b v) ≤ ∫ v in Ioi y, 2 / (Real.pi * b) * v ^ (-2 : ℝ) := by
      apply setIntegral_mono_on hi.integrableOn hp measurableSet_Ioi
      intro v hv
      have hv0 : 0 < v := hy.trans hv
      convert K_bound hb hv0.ne' using 1
      rw [Real.rpow_neg (le_of_lt hv0), Real.rpow_two]
      ring
    _ = 2 / (Real.pi * b * y) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ)< -1) hy]
      norm_num [Real.rpow_neg_one]
      ring

private lemma H_tail {b U : ℝ} (hb : 0 < b) (hi : Integrable (K b))
    (hh : Integrable (H b U)) {y : ℝ} (hy : 0 < y) :
    (∫ v in Set.Ici y, H b U v) ≤ 4 / (Real.pi * b * y) := by
  calc
    (∫ v in Ici y, H b U v) ≤ ∫ v in Ici y, 2 * K b v :=
      setIntegral_mono_on hh.integrableOn (hi.const_mul 2).integrableOn measurableSet_Ici
        (fun v _ => H_le hb U v)
    _ = 2 * ∫ v in Ici y, K b v := integral_const_mul _ _
    _ ≤ 4 / (Real.pi * b * y) := by
      have := K_tail hb hi hy
      calc
        2 * ∫ v in Ici y, K b v ≤ 2 * (2 / (Real.pi * b * y)) := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 4 / (Real.pi * b * y) := by ring

private lemma K_ae (b : ℝ) : K b =ᵐ[volume] fejerKernel b := by
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with v hv
  have hv : v ≠ 0 := by simpa using hv
  by_cases hb : b = 0
  · simp [K, fejerKernel, hb]
  · have hx : b * v / 2 ≠ 0 := div_ne_zero (mul_ne_zero hb hv) (by norm_num)
    simp only [K, fejerKernel, Real.sinc_of_ne_zero hx]

private lemma K_integrable {b : ℝ} (hb : 0 < b) : Integrable (K b) := by
  have hi := (integrable_sin_div_sq.comp_mul_left' (show b / 2 ≠ 0 by positivity)).const_mul (b / (2 * Real.pi))
  have he (v : ℝ) : b / 2 * v = b * v / 2 := by ring
  have hf : Integrable (fejerKernel b) := by
    change Integrable (fun v : ℝ => b / (2 * Real.pi) *
      (Real.sin (b * v / 2) / (b * v / 2)) ^ 2)
    simpa only [he] using hi
  exact hf.congr (K_ae b).symm

private lemma K_mass {b : ℝ} (hb : 0 < b) : (∫ v, K b v) = 1 := by
  rw [integral_congr_ae (K_ae b), integral_fejerKernel hb]

private lemma aft_fourier (g : ℝ → ℝ) (t : ℝ) :
    aft g t = 𝓕 (fun v => (g v : ℂ)) (t / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [smul_eq_mul]
  have he : (((-2 * Real.pi * v * (t / (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
      -Complex.I * (t : ℂ) * (v : ℂ) := by
    push_cast
    field_simp
  rw [he, mul_comm]

private lemma K_gTent_ae {b : ℝ} (hb : 0 < b) :
    (fun v => (K b v : ℂ)) =ᵐ[volume] gTent (b / (2 * Real.pi)) 0 := by
  filter_upwards [K_ae b] with v hv
  rw [hv]
  simp only [gTent, sqSincC, fejerKernel, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, one_mul]
  have he : Real.pi * (b / (2 * Real.pi) * v) = b * v / 2 := by field_simp
  rw [he]
  push_cast
  rfl

private lemma K_aft {b : ℝ} (hb : 0 < b) (t : ℝ) :
    aft (K b) t = (phi b t : ℂ) := by
  rw [aft_fourier, Real.fourier_congr_ae (K_gTent_ae hb),
    fourier_gTent (by positivity) 0]
  have he : (t / (2 * Real.pi) - 0) / (b / (2 * Real.pi)) = t / b := by field_simp; ring
  rw [he]
  simp [tentC, tent, phi, abs_div, abs_of_pos hb]


private lemma aft_integrable {g : ℝ → ℝ} (hg : Integrable g) (t : ℝ) :
    Integrable (fun v : ℝ => (g v : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ))) := by
  refine hg.ofReal.mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards [] with v
  have he : -Complex.I * (t : ℂ) * (v : ℂ) = ((-t * v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [he, Complex.norm_exp_ofReal_mul_I]

private lemma aft_zero (g : ℝ → ℝ) : aft g 0 = ((∫ v, g v) : ℂ) := by
  simp only [aft, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]

private lemma H_integrable {b : ℝ} (hb : 0 < b) (U : ℝ) : Integrable (H b U) := by
  apply (K_integrable hb).mul_bdd (c := 2) (by fun_prop)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
  linarith [Real.neg_one_le_cos (U * v)]

private lemma H_aft {b : ℝ} (hb : 0 < b) (U t : ℝ) :
    aft (H b U) t = (psi b U t : ℂ) := by
  have he (v : ℝ) :
      ((H b U v : ℝ) : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ)) =
      ((K b v : ℝ) : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ)) -
      ((K b v : ℝ) : ℂ) * Complex.exp (-Complex.I * ((t-U : ℝ) : ℂ) * (v : ℂ)) / 2 -
      ((K b v : ℝ) : ℂ) * Complex.exp (-Complex.I * ((t+U : ℝ) : ℂ) * (v : ℂ)) / 2 := by
    have hm : Complex.exp (-Complex.I * ((t-U : ℝ) : ℂ) * (v : ℂ)) =
        Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (((U*v : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hp : Complex.exp (-Complex.I * ((t+U : ℝ) : ℂ) * (v : ℂ)) =
        Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ)) *
        Complex.exp (-((U*v : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hm, hp]
    have hc : (Real.cos (U*v) : ℂ) =
        (Complex.exp (((U*v : ℝ) : ℂ) * Complex.I) +
          Complex.exp (-((U*v : ℝ) : ℂ) * Complex.I)) / 2 := by
      rw [Complex.ofReal_cos]
      rfl
    simp only [H, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    rw [hc]; push_cast; ring
  have hi₀ := aft_integrable (K_integrable hb) t
  have hi₁ := (aft_integrable (K_integrable hb) (t-U)).div_const 2
  have hi₂ := (aft_integrable (K_integrable hb) (t+U)).div_const 2
  have his : Integrable (fun v : ℝ =>
      (K b v : ℂ) * Complex.exp (-Complex.I * (t : ℂ) * (v : ℂ)) -
      (K b v : ℂ) * Complex.exp (-Complex.I * ((t-U : ℝ) : ℂ) * (v : ℂ)) / 2) :=
    hi₀.sub hi₁
  unfold aft
  rw [integral_congr_ae (Eventually.of_forall he),
    integral_sub his hi₂,
    integral_sub hi₀ hi₁,
    integral_div, integral_div]
  change aft (K b) t - aft (K b) (t-U) / 2 - aft (K b) (t+U) / 2 = _
  rw [K_aft hb, K_aft hb, K_aft hb]
  simp only [psi, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]

private lemma H_mass {b U : ℝ} (hb : 0 < b) (hU : 2*b < U) :
    (∫ v, H b U v) = 1 := by
  have hz : psi b U 0 = 1 := by
    have hu : 0 < U := by linarith
    have hd : 1 ≤ U / b := (le_div_iff₀ hb).mpr (by linarith)
    simp [psi, phi, abs_of_pos hu, max_eq_left (by linarith : 1 - U / b ≤ 0)]
  have h := H_aft hb U 0
  rw [aft_zero, hz, Complex.ofReal_one] at h
  exact_mod_cast h


private lemma log_K_decay {b : ℝ} (hb : 0 < b)
    (htail : ∀ v : ℝ, v ≠ 0 → K b v ≤ 2 / (Real.pi * b * v ^ 2)) (v : ℝ) :
    K b v ≤ (4 * (b / (2 * Real.pi) + 2 / (Real.pi * b))) /
      (1 + |v|) ^ 2 := by
  have hp := Real.pi_pos
  have hx : 0 < 1 + |v| := by positivity
  rw [le_div_iff₀ (sq_pos_of_pos hx)]
  by_cases hv : |v| ≤ 1
  · have hsq : (1 + |v|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg v]
    have hk := K_cap hb v
    have hk0 := K_nonneg hb v
    have hpos : 0 ≤ b / (2 * Real.pi) := by positivity
    calc
      K b v * (1 + |v|) ^ 2 ≤ (b / (2 * Real.pi)) * 4 :=
        mul_le_mul hk hsq (sq_nonneg _) hpos
      _ ≤ 4 * (b / (2 * Real.pi) + 2 / (Real.pi * b)) := by
        have : 0 ≤ 2 / (Real.pi * b) := by positivity
        nlinarith
  · have hv1 : 1 < |v| := lt_of_not_ge hv
    have hv0 : v ≠ 0 := by intro h; simp [h] at hv1; linarith
    have hsq : (1 + |v|) ^ 2 ≤ 4 * v ^ 2 := by
      nlinarith [sq_abs v, abs_nonneg v]
    have hk := htail v hv0
    have hden : 0 < Real.pi * b * v ^ 2 := by positivity
    calc
      K b v * (1 + |v|) ^ 2 ≤ (2 / (Real.pi * b * v ^ 2)) * (4 * v ^ 2) :=
        mul_le_mul hk hsq (sq_nonneg _) (by positivity)
      _ = 4 * (2 / (Real.pi * b)) := by field_simp
      _ ≤ 4 * (b / (2 * Real.pi) + 2 / (Real.pi * b)) := by
        have : 0 ≤ b / (2 * Real.pi) := by positivity
        linarith

private lemma log_moment_integrable {b : ℝ} (hb : 0 < b)
    (htail : ∀ v : ℝ, v ≠ 0 → K b v ≤ 2 / (Real.pi * b * v ^ 2)) :
    Integrable (fun v => K b v * Real.log (1 + |v|)) := by
  let A : ℝ := 4 * (b / (2 * Real.pi) + 2 / (Real.pi * b))
  have hi : Integrable (fun v : ℝ => (1 + |v|) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := (3 / 2 : ℝ)) (by norm_num))
  refine (hi.const_mul (2 * A)).mono' ?_ (ae_of_all _ fun v => ?_)
  · exact ((K_continuous b).mul
      ((show Continuous (fun v : ℝ => 1 + |v|) by fun_prop).log (by intro v; positivity))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (K_nonneg hb v)
        (Real.log_nonneg (by linarith [abs_nonneg v])))]
    have hx : 0 < 1 + |v| := by positivity
    have hlog := Real.log_le_rpow_div (x := 1 + |v|) (ε := (1 / 2 : ℝ)) (by positivity) (by norm_num)
    have hk := log_K_decay hb htail v
    calc
      K b v * Real.log (1 + |v|) ≤ (A / (1 + |v|) ^ 2) * ((1 + |v|) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) :=
        mul_le_mul hk hlog (Real.log_nonneg (by linarith [abs_nonneg v])) (by dsimp [A]; positivity)
      _ = 2 * A * (1 + |v|) ^ (-(3 / 2 : ℝ)) := by
        have hr : (1 + |v|) ^ (-(3 / 2 : ℝ)) =
            (1 + |v|) ^ (1 / 2 : ℝ) / (1 + |v|) ^ 2 := by
          rw [← Real.rpow_natCast (1 + |v|) 2, ← Real.rpow_sub hx]
          norm_num
        rw [hr]
        ring

private lemma log_ell_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ ell u := by
  apply Real.log_nonneg
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  linarith

private lemma log_ell_shift {u y : ℝ} (hu : 0 ≤ u) (hy : 0 ≤ y) :
    ell u ≤ ell y + Real.log (1 + |y - u|) := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have heu : 0 < Real.exp 1 + u := by positivity
  have hey : 0 < Real.exp 1 + y := by positivity
  have hx : 0 < 1 + |y - u| := by positivity
  unfold ell
  rw [← Real.log_mul hey.ne' hx.ne']
  apply Real.log_le_log heu
  have ha := neg_le_abs (y - u)
  have ha0 := abs_nonneg (y - u)
  nlinarith

private lemma log_average_of_moment (g : ℝ → ℝ) (hg : Integrable g)
    (hpos : ∀ v, 0 ≤ g v) (hmass : (∫ v, g v) = 1)
    (hmoment : Integrable (fun v => g v * Real.log (1 + |v|)))
    {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fun u => g (y - u) * ell u) (Ici 0) ∧
    (∫ u in Ici 0, g (y - u) * ell u) ≤
      ell y + ∫ v, g v * Real.log (1 + |v|) := by
  have hgy := hg.comp_sub_left y
  have hmy := hmoment.comp_sub_left y
  have hmajor : Integrable (fun u => ell y * g (y - u) +
      g (y - u) * Real.log (1 + |y - u|)) :=
    (hgy.const_mul (ell y)).add hmy
  have hint : IntegrableOn (fun u => g (y - u) * ell u) (Ici 0) := by
    refine hmajor.integrableOn.mono' ?_ ?_
    · exact (hgy.aestronglyMeasurable.mul
        (show Measurable ell by unfold ell; fun_prop).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _) (log_ell_nonneg hu))]
      calc
        g (y - u) * ell u ≤ g (y - u) * (ell y + Real.log (1 + |y - u|)) :=
          mul_le_mul_of_nonneg_left (log_ell_shift hu hy) (hpos _)
        _ = _ := by ring
  refine ⟨hint, ?_⟩
  calc
    (∫ u in Ici 0, g (y - u) * ell u) ≤
        ∫ u in Ici 0, ell y * g (y - u) + g (y - u) * Real.log (1 + |y - u|) := by
      apply integral_mono_ae hint hmajor.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      have := mul_le_mul_of_nonneg_left (log_ell_shift hu hy) (hpos (y - u))
      nlinarith
    _ = ell y * (∫ u in Ici 0, g (y - u)) +
        ∫ u in Ici 0, g (y - u) * Real.log (1 + |y - u|) := by
      rw [integral_add (hgy.integrableOn.const_mul _) hmy.integrableOn, integral_const_mul]
    _ ≤ ell y * (∫ u, g (y - u)) +
        ∫ u, g (y - u) * Real.log (1 + |y - u|) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hgy (ae_of_all _ fun u => hpos _))
          (log_ell_nonneg hy)
      · exact setIntegral_le_integral hmy (ae_of_all _ fun u =>
          mul_nonneg (hpos _) (Real.log_nonneg (by linarith [abs_nonneg (y - u)])))
    _ = _ := by
      rw [integral_sub_left_eq_self g volume y,
        integral_sub_left_eq_self (fun v => g v * Real.log (1 + |v|)) volume y,
        hmass, mul_one]

private lemma log_K_scale (M v : ℝ) : K M v = M * K 1 (M * v) := by
  simp only [K, one_mul]
  ring

private lemma log_scaled_moment_le {M : ℝ} (hM : 1 ≤ M)
    (h1 : Integrable (fun v => K 1 v * Real.log (1 + |v|))) :
    (∫ v, K M v * Real.log (1 + |v|)) ≤
      ∫ v, K 1 v * Real.log (1 + |v|) := by
  have hM0 : 0 < M := by linarith
  let q : ℝ → ℝ := fun w => K 1 w * Real.log (1 + |w| / M)
  have hq_le (w : ℝ) : q w ≤ K 1 w * Real.log (1 + |w|) := by
    apply mul_le_mul_of_nonneg_left _ (K_nonneg zero_lt_one w)
    apply Real.log_le_log (by positivity)
    have : |w| / M ≤ |w| := (div_le_self (abs_nonneg w) hM)
    linarith
  have hq_nonneg (w : ℝ) : 0 ≤ q w :=
    mul_nonneg (K_nonneg zero_lt_one w)
      (Real.log_nonneg (by have := div_nonneg (abs_nonneg w) hM0.le; linarith))
  have hq : Integrable q := by
    apply h1.mono' _ (ae_of_all _ fun w => ?_)
    · exact ((K_continuous 1).mul
        ((show Continuous (fun w : ℝ => 1 + |w| / M) by fun_prop).log (by intro w; positivity))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hq_nonneg w)]
      exact hq_le w
  have heq (v : ℝ) : K M v * Real.log (1 + |v|) = M * q (M * v) := by
    rw [log_K_scale]
    dsimp [q]
    rw [abs_mul, abs_of_pos hM0]
    have hdiv : M * |v| / M = |v| := by field_simp
    rw [hdiv]
    ring
  calc
    (∫ v, K M v * Real.log (1 + |v|)) = M * ∫ v, q (M * v) := by
      simp_rw [heq]
      exact integral_const_mul _ _
    _ = ∫ v, q v := by
      rw [Measure.integral_comp_mul_left, smul_eq_mul, abs_of_pos (inv_pos.mpr hM0)]
      field_simp
    _ ≤ _ := integral_mono hq h1 hq_le

private lemma log_H_moment_integrable {b : ℝ} (_hb : 0 < b) (U : ℝ)
    (hle : ∀ v, 0 ≤ H b U v ∧ H b U v ≤ 2 * K b v)
    (hk : Integrable (fun v => K b v * Real.log (1 + |v|))) :
    Integrable (fun v => H b U v * Real.log (1 + |v|)) := by
  refine (hk.const_mul 2).mono' ?_ (ae_of_all _ fun v => ?_)
  · exact ((H_continuous b U).mul
      ((show Continuous (fun v : ℝ => 1 + |v|) by fun_prop).log (by intro v; positivity))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hle v).1
        (Real.log_nonneg (by linarith [abs_nonneg v])))]
    have h := mul_le_mul_of_nonneg_right (hle v).2
      (Real.log_nonneg (show 1 ≤ 1 + |v| by linarith [abs_nonneg v]))
    nlinarith

private lemma log_H_moment_le {b : ℝ} (hb : 0 < b) (U : ℝ)
    (hle : ∀ v, 0 ≤ H b U v ∧ H b U v ≤ 2 * K b v)
    (hk : Integrable (fun v => K b v * Real.log (1 + |v|))) :
    (∫ v, H b U v * Real.log (1 + |v|)) ≤
      2 * ∫ v, K b v * Real.log (1 + |v|) := by
  rw [← integral_const_mul]
  apply integral_mono (log_H_moment_integrable hb U hle hk) (hk.const_mul 2)
  intro v
  have h := mul_le_mul_of_nonneg_right (hle v).2
    (Real.log_nonneg (show 1 ≤ 1 + |v| by linarith [abs_nonneg v]))
  nlinarith

private lemma log_fejer_average
    (hki : ∀ b : ℝ, 0 < b → Integrable (K b))
    (hkmass : ∀ b : ℝ, 0 < b → (∫ v, K b v) = 1)
    (hktail : ∀ b : ℝ, 0 < b → ∀ v : ℝ, v ≠ 0 → K b v ≤ 2 / (Real.pi * b * v ^ 2)) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ M y : ℝ, 1 ≤ M → 1 ≤ y →
      IntegrableOn (fun u => K M (y - u) * ell u) (Set.Ici 0) ∧
      (∫ u in Set.Ici 0, K M (y - u) * ell u) ≤ ell y + C₀ := by
  have hmoment1 := log_moment_integrable zero_lt_one (hktail 1 zero_lt_one)
  refine ⟨∫ v, K 1 v * Real.log (1 + |v|), ?_, ?_⟩
  · apply integral_nonneg
    intro v
    exact mul_nonneg (K_nonneg zero_lt_one v)
      (Real.log_nonneg (by linarith [abs_nonneg v]))
  · intro M y hM hy
    have hM0 : 0 < M := by linarith
    have hmomentM := log_moment_integrable hM0 (hktail M hM0)
    obtain ⟨hi, hbound⟩ := log_average_of_moment (K M) (hki M hM0)
      (K_nonneg hM0) (hkmass M hM0) hmomentM (by linarith : 0 ≤ y)
    exact ⟨hi, hbound.trans (add_le_add le_rfl (log_scaled_moment_le hM hmoment1))⟩

private lemma log_notched_average {b : ℝ} (hb : 0 < b)
    (hktail : ∀ v : ℝ, v ≠ 0 → K b v ≤ 2 / (Real.pi * b * v ^ 2))
    (hhi : ∀ U : ℝ, Integrable (H b U))
    (hhmass : ∀ U : ℝ, 2 * b < U → (∫ v, H b U v) = 1)
    (hhle : ∀ U v : ℝ, 0 ≤ H b U v ∧ H b U v ≤ 2 * K b v) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ U y : ℝ, 2 * b < U → 1 ≤ y →
      IntegrableOn (fun u => H b U (y - u) * ell u) (Set.Ici 0) ∧
      (∫ u in Set.Ici 0, H b U (y - u) * ell u) ≤ ell y + Cb := by
  have hmoment := log_moment_integrable hb hktail
  refine ⟨2 * ∫ v, K b v * Real.log (1 + |v|), ?_, ?_⟩
  · apply mul_nonneg (by norm_num)
    apply integral_nonneg
    intro v
    exact mul_nonneg (K_nonneg hb v)
      (Real.log_nonneg (by linarith [abs_nonneg v]))
  · intro U y hU hy
    have hHmoment := log_H_moment_integrable hb U (hhle U) hmoment
    obtain ⟨hi, hbound⟩ := log_average_of_moment (H b U) (hhi U)
      (fun v => (hhle U v).1) (hhmass U hU) hHmoment (by linarith : 0 ≤ y)
    exact ⟨hi, hbound.trans (add_le_add le_rfl (log_H_moment_le hb U (hhle U) hmoment))⟩


theorem fejer_law {b : ℝ} (hb : 0 < b) :
    (∀ v, 0 ≤ K b v) ∧ Integrable (K b) ∧ (∫ v, K b v) = 1 ∧
    (∀ t, aft (K b) t = (phi b t : ℂ)) ∧
    (∀ y : ℝ, 0 < y → (∫ v in Set.Ici y, K b v) ≤ 2 / (Real.pi * b * y)) := by
  exact ⟨K_nonneg hb, K_integrable hb, K_mass hb, K_aft hb,
    fun _ hy => K_tail hb (K_integrable hb) hy⟩

theorem notched_fejer_law {b U : ℝ} (hb : 0 < b) (hU : 2 * b < U) :
    (∀ v, 0 ≤ H b U v ∧ H b U v ≤ 2 * K b v) ∧ Integrable (H b U) ∧
    (∫ v, H b U v) = 1 ∧ (∀ t, aft (H b U) t = (psi b U t : ℂ)) ∧
    (∀ y : ℝ, 0 < y → (∫ v in Set.Ici y, H b U v) ≤ 4 / (Real.pi * b * y)) := by
  exact ⟨fun v => ⟨H_nonneg hb U v, H_le hb U v⟩,
    H_integrable hb U, H_mass hb hU, H_aft hb U,
    fun _ hy => H_tail hb (K_integrable hb) (H_integrable hb U) hy⟩


theorem fejer_log_average :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ M y : ℝ, 1 ≤ M → 1 ≤ y →
      IntegrableOn (fun u => K M (y - u) * ell u) (Set.Ici 0) ∧
      (∫ u in Set.Ici 0, K M (y - u) * ell u) ≤ ell y + C₀ := by
  exact log_fejer_average (fun _ hb => K_integrable hb) (fun _ hb => K_mass hb)
    (fun _ hb _ hv => K_bound hb hv)

theorem notched_log_average {b : ℝ} (hb : 0 < b) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ U y : ℝ, 2 * b < U → 1 ≤ y →
      IntegrableOn (fun u => H b U (y - u) * ell u) (Set.Ici 0) ∧
      (∫ u in Set.Ici 0, H b U (y - u) * ell u) ≤ ell y + Cb := by
  exact log_notched_average hb (fun _ hv => K_bound hb hv)
    (H_integrable hb) (fun _ hU => H_mass hb hU)
    (fun U v => ⟨H_nonneg hb U v, H_le hb U v⟩)

end
end D5.S3.Analytic.Fourier.AngularFejerKernel
