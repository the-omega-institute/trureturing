/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondSchwinger4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent Schwinger normalization and the modified Bessel integral correction. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondBesselSeries4D
import D5.S3.Analytic.GammaGammaNBU.Result
import D5.S3.Analysis.SchwingerAsymptotics
import D5.S3.Analysis.SchwingerBessel
import D5.S3.Analysis.SingularSecondOrder

/-! The Schwinger integral fixes the logarithmic normalization on the positive axis. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace NullConeGravity

open D5.S3.Analytic.GammaGammaNBU.Result (besselK)

def schwingerH (t : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), Real.exp (-s - t / s)

private theorem hasDerivAt_schwingerH {t : ℝ} (ht : 0 < t) :
    HasDerivAt schwingerH (-Omega.schwingerMoment 1 t) t :=
  Omega.hasDerivAt_schwingerIntegral ht

theorem schwingerH_eq_series {t : ℝ} (ht : 0 < t) :
    (schwingerH t : ℂ) =
      1 + (t : ℂ) * ((Real.log t : ℂ) * besselP t - besselB t) := by
  let f : ℝ → ℂ := fun s => (schwingerH s : ℂ) - besselSeries s
  let g : ℝ → ℂ := fun s => ((-Omega.schwingerMoment 1 s : ℝ) : ℂ) - besselSeriesSlope s
  have hf (s : ℝ) (hs : 0 < s) : HasDerivAt f (g s) s :=
    (hasDerivAt_schwingerH hs).ofReal_comp.sub (hasDerivAt_besselSeries hs)
  have hg (s : ℝ) (hs : 0 < s) : HasDerivAt g (s⁻¹ • f s) s := by
    have h := ((Omega.hasDerivAt_schwingerMoment 1 hs).neg.ofReal_comp).sub
      (hasDerivAt_besselSeriesSlope hs)
    convert h using 1
    rw [Complex.real_smul]
    unfold f
    push_cast
    have hn : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    have hode : (schwingerH s : ℂ) = (s : ℂ) * (Omega.schwingerMoment 2 s : ℂ) := by
      exact_mod_cast Omega.schwingerIntegral_eq_mul_moment_two hs
    rw [hode]
    field_simp [hn]
    <;> ring
  have hH : Tendsto (fun s => (schwingerH s : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    change Tendsto (Complex.ofReal ∘ Omega.schwingerIntegral) (𝓝[>] 0) (𝓝 1)
    simpa only [Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).comp Omega.tendsto_schwingerIntegral_zero
  have hf₀ : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self] using hH.sub tendsto_besselSeries_zero
  have hgH : Tendsto (fun s : ℝ => ((-Omega.schwingerMoment 1 s - Real.log s : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((2 * Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp Omega.tendsto_neg_schwingerMoment_one_sub_log
  have hg₀ : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have he : g = fun s =>
        ((-Omega.schwingerMoment 1 s - Real.log s : ℝ) : ℂ) -
        (besselSeriesSlope s - (Real.log s : ℂ)) := by
      ext s
      unfold g
      push_cast
      ring
    rw [he]
    simpa only [sub_self] using hgH.sub tendsto_besselSeriesSlope_sub_log
  exact sub_eq_zero.mp (Omega.eq_zero_of_singularSecondOrder hf hg hf₀ hg₀ ht)

private theorem besselSeriesSlope_eq_neg_moment {t : ℝ} (ht : 0 < t) :
    besselSeriesSlope t = ((-Omega.schwingerMoment 1 t : ℝ) : ℂ) := by
  apply (hasDerivAt_besselSeries ht).unique
  apply (hasDerivAt_schwingerH ht).ofReal_comp.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact (schwingerH_eq_series hs).symm

theorem correction_eq_besselK {M u v x : ℝ}
    (hM : 0 < M) (hu : 0 < u) (hv : 0 < v) (hx : x < 1) :
    let z := M * Real.sqrt (2*u*v*(1-x))
    correction M u v x =
      ((M^2 / (16 * Real.pi^2) * (z * besselK 1 z - 2 * besselK 0 z) : ℝ) : ℂ) := by
  let q : ℝ := 2*u*v*(1-x)
  let t : ℝ := M^2*u*v*(1-x)/2
  let z : ℝ := M * Real.sqrt q
  have hq : 0 < q := by dsimp [q]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hz : 0 < z := mul_pos hM (Real.sqrt_pos_of_pos hq)
  have ht_z : 2 * Real.sqrt t = z := by
    have hs : (2 * Real.sqrt t)^2 = z^2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]
      dsimp [z]
      rw [mul_pow, Real.sq_sqrt hq.le]
      dsimp [q, t]
      ring
    have hr : 0 < Real.sqrt t := Real.sqrt_pos_of_pos ht
    nlinarith [sq_nonneg (2 * Real.sqrt t - z)]
  have hk0 : Omega.schwingerMoment 1 t = 2 * besselK 0 z := by
    simpa only [besselK, zero_mul, Real.cosh_zero, mul_one, ht_z] using
      Omega.schwingerMoment_one_eq_cosh_integral ht
  have hk1 : schwingerH t = z * besselK 1 z := by
    change Omega.schwingerIntegral t = _
    simpa only [besselK, one_mul, ht_z] using Omega.schwingerIntegral_eq_cosh_integral ht
  have hs : besselSeries t = (schwingerH t : ℂ) := (schwingerH_eq_series ht).symm
  change correction M u v x = ((M^2 / (16 * Real.pi^2) *
    (z * besselK 1 z - 2 * besselK 0 z) : ℝ) : ℂ)
  rw [correction, ite_eq_left hx]
  change correctionLog M t (Real.log t) = _
  rw [correctionLog_eq_series, hs, besselSeriesSlope_eq_neg_moment ht, hk0, hk1]
  push_cast
  ring

end NullConeGravity
