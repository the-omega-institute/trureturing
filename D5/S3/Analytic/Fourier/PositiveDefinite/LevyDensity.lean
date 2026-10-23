/- GID: D5/S3/Analytic/Fourier/PositiveDefinite/LevyDensity
   generality: I
   mirror-B: D5/B/S3/Analytic/Fourier/PositiveDefinite/LevyDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.DominatedConvergence, mathlib/module/Mathlib.Analysis.SpecificLimits.Basic]
   utility: none
   digest: Positive cosine mixtures, compound Poisson exponentials and integrable density limits. -/

import D5.S3.Analytic.Fourier.PositiveDefinite.Closure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! A finite density gives a compound Poisson exponential; dominated convergence removes truncation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
open D5.S3.Weil.ZetaLinear.FiniteInversePoissonCriterion

namespace D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity

/-- Integrable nonnegative densities give positive compound Poisson exponentials. -/
theorem finite_density {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : ∀ᵐ s ∂μ, 0 ≤ d s) (hi : Integrable d μ) {r : ℝ} (hr : 0 ≤ r) :
    PositiveDefinite (fun t => (Real.exp (-r *
      (∫ s, (1 - Real.cos (t * s)) * d s ∂μ)) : ℂ)) := by
  have hc (t : ℝ) : Integrable (fun s => Real.cos (t * s) * d s) μ :=
    hi.bdd_mul (by fun_prop) (Eventually.of_forall fun s => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * s))
  have HA : PositiveDefinite (fun t => (∫ s, Real.cos (t * s) * d s ∂μ : ℝ)) := by
    have H := Closure.integral
      (f := fun s t => ((d s : ℂ) * (Real.cos (s * t) : ℂ)))
      (hd.mono fun s hs => Closure.smul (Closure.cos s) hs)
      (fun t => by simpa [mul_comm] using (hc t).ofReal (𝕜 := ℂ))
    have HH (t : ℝ) : (∫ s, (d s : ℂ) * (Real.cos (s * t) : ℂ) ∂μ) =
        Complex.ofReal (∫ s, Real.cos (t * s) * d s ∂μ) := by
      calc
        _ = ∫ s, Complex.ofReal (Real.cos (t * s) * d s) ∂μ := by
          congr 1
          funext s
          push_cast
          rw [mul_comm (s : ℂ) (t : ℂ), mul_comm]
        _ = _ := integral_ofReal
    convert H using 1
    funext t
    exact (HH t).symm
  have HE := Closure.smul (Closure.exp (Closure.smul HA hr))
    (a := Real.exp (-r * ∫ s, d s ∂μ)) (Real.exp_pos _).le
  convert HE using 1
  funext t
  have Hid : (∫ s, (1 - Real.cos (t * s)) * d s ∂μ) =
      (∫ s, d s ∂μ) - ∫ s, Real.cos (t * s) * d s ∂μ := by
    rw [← integral_sub hi (hc t)]
    congr 1
    funext s
    ring
  rw [Hid]
  simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_sub, ← Complex.exp_add]
  congr 1
  ring

/-- Exhausting integrable truncations yield the full cosine-deficit exponential. -/
theorem of_truncations {μ : Measure ℝ} {d : ℝ → ℝ}
    (hd : ∀ᵐ s ∂μ, 0 ≤ d s) (K : ℕ → Set ℝ)
    (hK : ∀ n, MeasurableSet (K n))
    (hcover : ∀ᵐ s ∂μ, ∀ᶠ n in atTop, s ∈ K n)
    (hlocal : ∀ n, IntegrableOn d (K n) μ)
    (hi : ∀ t, Integrable (fun s => (1 - Real.cos (t * s)) * d s) μ)
    {r : ℝ} (hr : 0 ≤ r) :
    PositiveDefinite (fun t => (Real.exp (-r *
      (∫ s, (1 - Real.cos (t * s)) * d s ∂μ)) : ℂ)) := by
  apply Closure.limit (l := atTop)
    (f := fun n t => (Real.exp (-r *
      (∫ s in K n, (1 - Real.cos (t * s)) * d s ∂μ)) : ℂ))
  · intro n
    exact finite_density (ae_restrict_of_ae hd) (hlocal n) hr
  · intro t
    have H := tendsto_integral_of_dominated_convergence
      (μ := μ) (f := fun s => (1 - Real.cos (t * s)) * d s) (F := fun n => (K n).indicator (fun s => (1 - Real.cos (t * s)) * d s))
      (fun s => ‖(1 - Real.cos (t * s)) * d s‖)
      (fun n => (hi t).aestronglyMeasurable.indicator (hK n))
      (hi t).norm
      (fun n => Eventually.of_forall fun s => by
        by_cases hs : s ∈ K n
        · rw [Set.indicator_of_mem hs]
        · rw [Set.indicator_of_notMem hs, norm_zero]
          exact norm_nonneg _)
      (hcover.mono fun s hs => tendsto_const_nhds.congr' (hs.mono fun n hn => by
        simp only [Set.indicator_of_mem hn]))
    simp_rw [integral_indicator (hK _)] at H
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.mul H))

/-- The positive-half-line Levy density criterion in the local integrability form. -/
theorem positiveDefinite {D : ℝ → ℝ} (hD : ∀ s, 0 < s → 0 ≤ D s)
    (hlocal : ∀ n : ℕ, IntegrableOn (fun s => D s / s)
      (Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)))
    (hi : ∀ t, IntegrableOn (fun s => (1 - Real.cos (t * s)) * D s / s) (Ioi 0))
    {r : ℝ} (hr : 0 < r) :
    PositiveDefinite (fun t => (Real.exp (-r * (2 *
      ∫ s in Ioi 0, (1 - Real.cos (t * s)) * D s / s)) : ℂ)) := by
  let K : ℕ → Set ℝ := fun n => Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
  have HK (n : ℕ) : K n ⊆ Ioi 0 := by
    intro s hs
    exact lt_of_lt_of_le (by positivity) hs.1
  have H := of_truncations (μ := volume.restrict (Ioi 0)) (d := fun s => D s / s)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact div_nonneg (hD s hs) hs.le)
    K (fun n => measurableSet_Icc)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < s :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hs)
      have hlarge : ∀ᶠ n : ℕ in atTop, s ≤ (n : ℝ) + 1 :=
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).eventually_ge_atTop s
      filter_upwards [hsmall, hlarge] with n hn hn'
      exact ⟨hn.le, hn'⟩)
    (fun n => by
      change Integrable _ ((volume.restrict (Ioi 0)).restrict (K n))
      rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr (HK n)]
      exact hlocal n)
    (fun t => by simpa only [IntegrableOn, div_eq_mul_inv, mul_assoc] using hi t)
    (r := 2 * r) (by positivity)
  convert H using 1
  funext t
  congr 2
  rw [show -r * (2 * ∫ s in Ioi 0, (1 - Real.cos (t * s)) * D s / s) =
      -(2 * r) * ∫ s in Ioi 0, (1 - Real.cos (t * s)) * D s / s by ring]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by ring

end D5.S3.Analytic.Fourier.PositiveDefinite.LevyDensity
