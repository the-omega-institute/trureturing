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

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
