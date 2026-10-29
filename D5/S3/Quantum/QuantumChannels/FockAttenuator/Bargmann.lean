/- GID: D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Entire factorial series and Gaussian evaluation control on the completed Fock space. -/

import D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic

/-!
The Bargmann transform uses the actual completed carrier and exponential
vectors of `BeamSplitter`. Its first inner-product argument contains the
complex conjugate of the analytic variable. Entire functions outside the
image are not assigned Fock vectors.

The classical analytic realization is attributed in
`Library/QuantumStates/bargmann1961analytic.md`. This module proves analytic
control for arbitrary square-summable coefficients. Finite separation,
reconstruction, and physical rank classification require further theorems.
-/

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal NNReal
open Filter Topology

namespace D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
open BeamSplitter

abbrev Fock := lp (fun _ : ℕ => ℂ) 2
abbrev TwoMode := lp (fun _ : ℕ => Fock) 2

/-- The entire transform, with the Hilbert-space conjugation convention made explicit. -/
def transform (a : Fock) (z : ℂ) : ℂ :=
  inner ℂ (exponentialVector ((starRingEnd ℂ) z)) a

/-- The factorial-normalized scalar power series of an arbitrary completed vector. -/
def series (a : Fock) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => a n / (Real.sqrt (n.factorial : ℝ) : ℂ))

theorem has_sum (a : Fock) (z : ℂ) :
    HasSum (fun n => a n * z ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ))
      (transform a z) := by
  change HasSum _ (inner ℂ (exponentialVector ((starRingEnd ℂ) z)) a)
  convert lp.hasSum_inner (𝕜 := ℂ) (exponentialVector ((starRingEnd ℂ) z)) a using 1
  ext n
  simp only [exponentialVector, exponentialCoeff, RCLike.inner_apply,
    map_div₀, map_pow, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- Absolute radial summability holds at every radius, including radius zero. -/
theorem summable_radial (a : Fock) (R : ℝ≥0) :
    Summable (fun n => ‖a n‖ * (R : ℝ) ^ n / Real.sqrt (n.factorial : ℝ)) := by
  have h := lp.summable_mul (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (by rw [Real.holderConjugate_iff]; norm_num) a (exponentialVector (R : ℂ))
  convert h using 1
  ext n
  simp only [exponentialVector, exponentialCoeff, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

theorem series_radius (a : Fock) : (series a).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro R
  convert summable_radial a R using 1
  ext n
  simp only [series, FormalMultilinearSeries.ofScalars_norm, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- The complete power series converges on the whole complex plane. -/
theorem has_fpower_series (a : Fock) :
    HasFPowerSeriesOnBall (transform a) (series a) 0 ⊤ := by
  refine ⟨by rw [series_radius], by simp, ?_⟩
  intro z _
  simpa only [zero_add, series, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, mul_div_assoc, div_mul_eq_mul_div] using has_sum a z

theorem entire (a : Fock) : Differentiable ℂ (transform a) := by
  intro z
  exact ((has_fpower_series a).analyticAt_of_mem (by simp)).differentiableAt

/-- The squared exponential-vector norm is the exponential of the squared parameter norm. -/
theorem exponential_norm_sq (z : ℂ) :
    ‖exponentialVector z‖ ^ 2 = Real.exp (‖z‖ ^ 2) := by
  have hnorm : HasSum (fun n => ‖exponentialVector z n‖ ^ 2)
      (‖exponentialVector z‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (exponentialVector z)
  have hexp : HasSum (fun n : ℕ => (‖z‖ ^ 2) ^ n / (n.factorial : ℝ))
      (Real.exp (‖z‖ ^ 2)) := by
    simpa only [Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (‖z‖ ^ 2)
  apply hnorm.unique
  convert hexp using 1
  ext n
  simp only [exponentialVector, exponentialCoeff, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (Nat.cast_nonneg n.factorial), pow_right_comm ‖z‖ n 2]

theorem exponential_norm (z : ℂ) :
    ‖exponentialVector z‖ = Real.exp (‖z‖ ^ 2 / 2) := by
  rw [Real.exp_half, ← exponential_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The full absolute radial sum obeys the Gaussian bound, without a support cutoff. -/
theorem tsum_radial_le (a : Fock) (R : ℝ≥0) :
    (∑' n, ‖a n‖ * (R : ℝ) ^ n / Real.sqrt (n.factorial : ℝ)) ≤
      ‖a‖ * Real.exp ((R : ℝ) ^ 2 / 2) := by
  have h := lp.tsum_mul_le_mul_norm'
    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (by rw [Real.holderConjugate_iff]; norm_num) a (exponentialVector (R : ℂ))
  rw [exponential_norm] at h
  simpa only [exponentialVector, exponentialCoeff, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg R.coe_nonneg,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_div_assoc] using h

/-- Gaussian evaluation control for arbitrary infinite-support Fock vectors. -/
theorem norm_transform_le (a : Fock) (z : ℂ) :
    ‖transform a z‖ ≤ ‖a‖ * Real.exp (‖z‖ ^ 2 / 2) := by
  have hradial := summable_radial a ⟨‖z‖, norm_nonneg z⟩
  change Summable (fun n => ‖a n‖ * ‖z‖ ^ n / Real.sqrt (n.factorial : ℝ)) at hradial
  have hbound := tsum_radial_le a ⟨‖z‖, norm_nonneg z⟩
  change (∑' n, ‖a n‖ * ‖z‖ ^ n / Real.sqrt (n.factorial : ℝ)) ≤
    ‖a‖ * Real.exp (‖z‖ ^ 2 / 2) at hbound
  have habs : Summable (fun n =>
      ‖a n * z ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)‖) := by
    simpa only [norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hradial
  calc
    ‖transform a z‖ = ‖∑' n, a n * z ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)‖ :=
      congrArg norm (has_sum a z).tsum_eq.symm
    _ ≤ ∑' n, ‖a n * z ^ n / (Real.sqrt (n.factorial : ℝ) : ℂ)‖ :=
      norm_tsum_le_tsum_norm habs
    _ ≤ ‖a‖ * Real.exp (‖z‖ ^ 2 / 2) := by
      simpa only [norm_div, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hbound

theorem transform_sub (a b : Fock) (z : ℂ) :
    transform (a - b) z = transform a z - transform b z :=
  inner_sub_right _ _ _

/-- A uniform estimate on each bounded disk, also controlling arbitrary Hilbert-norm limits. -/
theorem norm_transform_sub_le (a b : Fock) {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖transform a z - transform b z‖ ≤ ‖a - b‖ * Real.exp (R ^ 2 / 2) := by
  rw [← transform_sub]
  apply (norm_transform_le (a - b) z).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg z]

theorem uniform_power_series (a : Fock) (R : ℝ≥0) :
    TendstoUniformlyOn (fun n z => (series a).partialSum n z) (transform a) atTop
      (Metric.ball (0 : ℂ) R) := by
  simpa only [zero_add] using (has_fpower_series a).tendstoUniformlyOn (r' := R) (by simp)

/-- Equality of transforms recovers every original Hilbert coordinate. -/
theorem injective : Function.Injective transform := by
  intro a b hab
  have hp := (has_fpower_series a).hasFPowerSeriesAt
  rw [hab] at hp
  have hs := hp.eq_formalMultilinearSeries (has_fpower_series b).hasFPowerSeriesAt
  apply lp.ext
  funext n
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hs
  simp only [series, FormalMultilinearSeries.coeff_ofScalars] at hc
  exact (div_left_inj' (by
    norm_cast
    exact (Real.sqrt_pos.mpr (by positivity : 0 < (n.factorial : ℝ))).ne')).mp hc

/-- The transform as an injective complex-linear map into pointwise functions. -/
def transformLinear : Fock →ₗ[ℂ] (ℂ → ℂ) where
  toFun := transform
  map_add' a b := by funext z; exact inner_add_right _ _ _
  map_smul' c a := by funext z; exact inner_smul_right _ _ _

theorem transform_star (a : Fock) (w : ℂ) :
    transform (star a) w = inner ℂ a (exponentialVector w) := by
  apply (has_sum (star a) w).unique
  convert lp.hasSum_inner (𝕜 := ℂ) a (exponentialVector w) using 1
  ext n
  simp only [lp.star_apply, RCLike.inner_apply, exponentialVector, exponentialCoeff,
    starRingEnd_apply]
  ring

/-- Totalness is recovered from transform injectivity on the completed carrier. -/
theorem exponential_dense_span :
    (Submodule.span ℂ (Set.range exponentialVector)).topologicalClosure = ⊤ := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm
  · intro a ha
    have hzero : transform a = transform 0 := by
      funext z
      have hmem : exponentialVector ((starRingEnd ℂ) z) ∈
          Submodule.span ℂ (Set.range exponentialVector) :=
        Submodule.subset_span ⟨_, rfl⟩
      simpa only [transform, inner_zero_right] using
        Submodule.inner_right_of_mem_orthogonal hmem ha
    exact (Submodule.mem_bot ℂ).mpr (injective hzero)
  · exact bot_le

/-- Convergence in the completed Hilbert norm gives uniform convergence on every bounded disk. -/
theorem uniform_of_tendsto {ι : Type*} {l : Filter ι} {u : ι → Fock} {a : Fock}
    (hu : Tendsto u l (𝓝 a)) (R : ℝ≥0) :
    TendstoUniformlyOn (fun i => transform (u i)) (transform a) l
      (Metric.closedBall (0 : ℂ) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hC : 0 < Real.exp ((R : ℝ) ^ 2 / 2) := Real.exp_pos _
  have hevent : ∀ᶠ i in l, dist (u i) a < ε / Real.exp ((R : ℝ) ^ 2 / 2) :=
    (Metric.tendsto_nhds.mp hu) _ (div_pos hε hC)
  filter_upwards [hevent] with i hi z hz
  rw [dist_comm, dist_eq_norm]
  apply (norm_transform_sub_le (u i) a R.coe_nonneg (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz)).trans_lt
  exact (lt_div_iff₀ hC).mp (by simpa only [dist_eq_norm] using hi)

#print axioms injective
#print axioms uniform_of_tendsto

#print axioms has_fpower_series
#print axioms entire
#print axioms norm_transform_sub_le

end D5.S3.Quantum.QuantumChannels.FockAttenuator.Bargmann
