/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Grid
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Grid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite logistic grids with explicit cost and entropy errors. -/
import D5.S3.Weil.ZetaBridge.FermiMellin
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
open scoped Topology

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid

/-- Occupancy at logarithmic distance u from the central cutoff. -/
def logistic (u : ℝ) : ℝ := (1 + exp u)⁻¹
/-- The logarithmic Fermi weight. -/
def fermiLog (u : ℝ) : ℝ := log (1 + exp (-u))
/-- Entropy of the logistic occupancy. -/
def entropy (u : ℝ) : ℝ := binEntropy (logistic u)

private lemma logistic_range (u : ℝ) : 0 < logistic u ∧ logistic u < 1 := by
  have he := exp_pos u
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩

private lemma logistic_le_exp (u : ℝ) : logistic u ≤ exp (-u) := by
  rw [logistic, exp_neg]
  exact inv_anti₀ (exp_pos u) (by linarith)

private lemma logistic_continuous : Continuous logistic := by
  unfold logistic
  exact (continuous_const.add continuous_exp).inv₀ (fun u => by positivity)

private lemma fermiLog_deriv (u : ℝ) : HasDerivAt fermiLog (-logistic u) u := by
  have h := (((hasDerivAt_id u).neg.exp).const_add 1).log (by positivity : 1 + exp (-u) ≠ 0)
  convert h using 1
  · rfl
  · dsimp [logistic]
    rw [exp_neg]
    field_simp
    <;> ring

private lemma fermiLog_bounds (u : ℝ) : 0 ≤ fermiLog u ∧ fermiLog u ≤ exp (-u) := by
  constructor
  · exact log_nonneg (by linarith [exp_pos (-u)])
  · have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + exp (-u))
    simpa [fermiLog] using h

private lemma entropy_identity (u : ℝ) : entropy u = fermiLog u + u * logistic u := by
  have he := exp_pos u
  have hp : 1 - logistic u = exp u / (1 + exp u) := by
    dsimp [logistic]
    field_simp
    <;> ring
  have hn : 1 + exp u ≠ 0 := by positivity
  have hj : fermiLog u = log (1 + exp u) - u := by
    dsimp [fermiLog]
    rw [exp_neg, show 1 + (exp u)⁻¹ = (1 + exp u) / exp u by field_simp; ring,
      log_div hn he.ne', log_exp]
  rw [entropy, binEntropy, hp, logistic, inv_inv, log_inv, log_div he.ne' hn, log_exp, hj]
  field_simp
  <;> ring

private lemma fermi_real_one : IntegrableOn logistic (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), logistic u) = log 2 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable
    1 (by norm_num) 1 (by norm_num)
  have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_at_one 1 (by norm_num)
  have hp (u : ℝ) : ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re = logistic u := by
    simp [logistic, one_div, add_comm]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  have h := congrArg Complex.re he
  rw [← integral_re hi] at h
  simpa only [hp, Complex.ofReal_one, div_one, Complex.ofReal_re] using h

private lemma fermi_real_two : IntegrableOn (fun u => u * logistic u) (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), u * logistic u) = π ^ 2 / 12 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable
    1 (by norm_num) 2 (by norm_num)
  have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_eq_of_ne_one
    1 (by norm_num) 2 (by norm_num) (by norm_num)
  have hp (u : ℝ) : ((u : ℂ) ^ ((2 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re =
      u * logistic u := by
    norm_num [logistic, div_eq_mul_inv, add_comm, Complex.mul_re, Complex.inv_re]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  have h := congrArg Complex.re he
  rw [← integral_re hi] at h
  norm_num [hp, Complex.Gamma_nat_eq_factorial, riemannZeta_two,
    Complex.cpow_neg_one, Complex.mul_re, Complex.div_re] at h
  convert h using 1 <;> ring

private lemma exp_integrable : IntegrableOn (fun u : ℝ => exp (-u)) (Ioi 0) := by
  simpa using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0

private lemma fermiLog_integrable : IntegrableOn fermiLog (Ioi 0) := by
  apply exp_integrable.mono'
    ((continuous_iff_continuousAt.mpr (fun u => (fermiLog_deriv u).continuousAt)).aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (fermiLog_bounds u).1]
  exact (fermiLog_bounds u).2

private lemma mul_exp_limit : Tendsto (fun u : ℝ => u * exp (-u)) atTop (𝓝 0) := by
  simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)

private lemma mul_fermiLog_limit : Tendsto (fun u : ℝ => u * fermiLog u) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ mul_exp_limit
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg hu (fermiLog_bounds u).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_le_mul_of_nonneg_left (fermiLog_bounds u).2 hu

private lemma integral_fermiLog : (∫ u in Ioi (0 : ℝ), fermiLog u) = π ^ 2 / 12 := by
  have hd (u : ℝ) : HasDerivAt (fun v => v * fermiLog v)
      (fermiLog u - u * logistic u) u := by
    convert (hasDerivAt_id u).mul (fermiLog_deriv u) using 1 <;> simp <;> ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun u _ => hd u) (fermiLog_integrable.sub fermi_real_two.1) mul_fermiLog_limit
  rw [integral_sub fermiLog_integrable fermi_real_two.1, fermi_real_two.2] at h
  simp only [zero_mul, sub_zero] at h
  linarith

private lemma entropy_continuous : Continuous entropy :=
  binEntropy_continuous.comp logistic_continuous

private lemma entropy_integral : IntegrableOn entropy (Ioi 0) ∧
    (∫ u in Ioi (0 : ℝ), entropy u) = π ^ 2 / 6 := by
  refine ⟨(fermiLog_integrable.add fermi_real_two.1).congr
    (Eventually.of_forall (fun u => (entropy_identity u).symm)), ?_⟩
  simp_rw [entropy_identity]
  rw [integral_add fermiLog_integrable fermi_real_two.1, integral_fermiLog, fermi_real_two.2]
  ring

private lemma logistic_antitone : Antitone logistic := by
  intro u v huv
  exact inv_anti₀ (by positivity) (add_le_add_left (exp_le_exp.mpr huv) 1)

private lemma entropy_antitone : AntitoneOn entropy (Ici 0) := by
  intro u hu v hv huv
  apply binEntropy_strictMonoOn.monotoneOn
  · exact ⟨(logistic_range v).1.le, by
      have h := logistic_antitone hv
      simpa [logistic] using h⟩
  · exact ⟨(logistic_range u).1.le, by
      have h := logistic_antitone hu
      simpa [logistic] using h⟩
  · exact logistic_antitone huv

private lemma envelope_integrable :
    IntegrableOn (fun u : ℝ => (1 + u) * exp (-u)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => u * exp (-u)) (Ioi 0) := by
    simpa [mul_comm] using (GammaIntegral_convergent (s := 2) (by norm_num))
  simpa [add_mul] using exp_integrable.add h

private lemma envelope_tail {U : ℝ} (hU : 0 ≤ U) :
    (∫ u in Ioi U, (1 + u) * exp (-u)) = (U + 2) * exp (-U) := by
  have hi := envelope_integrable.mono_set (Ioi_subset_Ioi hU)
  have hl : Tendsto (fun u : ℝ => -(u + 2) * exp (-u)) atTop (𝓝 0) := by
    have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) :=
      tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa [add_mul, neg_add, neg_mul] using (mul_exp_limit.add (he.const_mul 2)).neg
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => -(v + 2) * exp (-v))
      ((1 + u) * exp (-u)) u := by
    convert (((hasDerivAt_id u).add_const 2).neg).mul ((hasDerivAt_id u).neg.exp) using 1
    <;> simp <;> ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) hi hl
  simpa using h

private lemma entropy_truncated {U : ℝ} (hU : 0 ≤ U) :
    π ^ 2 / 6 - (U + 2) * exp (-U) ≤ ∫ u in (0 : ℝ)..U, entropy u := by
  have hb : ∀ᵐ u ∂(volume.restrict (Ioi U)), entropy u ≤ (1 + u) * exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [entropy_identity, add_mul, one_mul]
    exact add_le_add (fermiLog_bounds u).2
      (mul_le_mul_of_nonneg_left (logistic_le_exp u) (hU.trans hu.le))
  have he := integral_mono_ae
    (entropy_integral.1.mono_set (Ioi_subset_Ioi hU))
    (envelope_integrable.mono_set (Ioi_subset_Ioi hU)) hb
  rw [envelope_tail hU] at he
  rw [← intervalIntegral.integral_Ioi_sub_Ioi entropy_integral.1 hU, entropy_integral.2]
  linarith

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
