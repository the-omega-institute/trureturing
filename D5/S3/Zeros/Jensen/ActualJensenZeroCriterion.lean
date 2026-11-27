/- GID: D5/S3/Zeros/Jensen/ActualJensenZeroCriterion
   generality: I
   mirror-B: D5/B/S3/Zeros/Jensen/ActualJensenZeroCriterion
   mirror-E: none(waiver:unbounded-analytic-construction)
   anchors: []
   utility: none
   digest: Real-rooted theta Jensen approximation implies standard RH by Cauchy's estimate. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
import D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
import D5.S3.Zeros.ActualZeroGeometry
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Zeros.Jensen.ActualJensenZeroCriterion

open Complex Filter Metric Polynomial Set MeasureTheory
open scoped Topology BigOperators
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.ActualZeroGeometry
open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open D5.S3.Analytic.Fourier.XiThetaTransform
open D5.S3.Analytic.Fourier.EvenGaussianMomentSeries
open private source_coefficients source_uniform_approximation source_at_zero
  from D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open private source_density_complex
  from D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open private source_map
  from D5.S3.Zeros.Jensen.SourceJensenIntegralExtension

/-- All complex roots of the polynomial are real. -/
def AllRootsReal (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → z.im = 0

/-- A locally uniform limit of polynomials with real roots, nonzero at the origin,
has only real zeros. Cauchy's order-zero bound for the reciprocal gives a direct
contradiction on any sufficiently small disk about a putative nonreal zero. -/
theorem allZerosReal_of_locallyUniform {ι : Type*} {l : Filter ι} [l.NeBot]
    (p : ι → ℂ[X]) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (h0 : F 0 ≠ 0) (hconv : TendstoLocallyUniformlyOn (fun i z => (p i).eval z) F l univ)
    (hroot : ∀ᶠ i in l, AllRootsReal (p i)) :
    ∀ c : ℂ, F c = 0 → c.im = 0 := by
  intro c hc
  by_contra hci
  have horder : analyticOrderAt F c ≠ ⊤ := by
    apply hF.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ (0 : ℂ)) (Set.mem_univ c)
    rw [(hF 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr h0]
    exact ENat.zero_ne_top
  have hpunct : ∀ᶠ z in 𝓝[≠] c, F z ≠ 0 := by
    apply (hF c (Set.mem_univ _)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    intro h
    exact horder (analyticOrderAt_eq_top.mpr h)
  rw [eventually_nhdsWithin_iff] at hpunct
  obtain ⟨e, he, hball⟩ := Metric.eventually_nhds_iff.mp hpunct
  let r : ℝ := min e |c.im| / 2
  have hr : 0 < r := div_pos (lt_min he (abs_pos.mpr hci)) (by norm_num)
  have hrl : r < e := by
    dsimp [r]
    linarith [min_le_left e |c.im|]
  have hri : r < |c.im| := by
    dsimp [r]
    linarith [min_le_right e |c.im|, abs_pos.mpr hci]
  have hnonreal (z : ℂ) (hz : z ∈ closedBall c r) : z.im ≠ 0 := by
    intro hzi
    have h := Complex.abs_im_le_norm (z - c)
    rw [Complex.sub_im, hzi, zero_sub, abs_neg] at h
    have hb : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    linarith
  have hcircle (z : ℂ) (hz : z ∈ sphere c r) : F z ≠ 0 := by
    have hdist : dist z c = r := mem_sphere.mp hz
    apply hball (by rw [hdist]; exact hrl)
    intro h
    subst z
    rw [dist_self] at hdist
    linarith
  obtain ⟨b, hb, hbmin⟩ := (isCompact_sphere c r).exists_forall_le'
    (hF.continuousOn.norm.mono (Set.subset_univ _))
    (fun z hz => norm_pos_iff.mpr (hcircle z hz))
  have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hconv
    (closedBall c r) (Set.subset_univ _) (isCompact_closedBall c r)
  have hErr := (tendstoUniformlyOn_iff.mp hU) (b / 4) (by positivity)
  obtain ⟨i, hiErr, hiRoot⟩ := (hErr.and hroot).exists
  have hpnonzero (z : ℂ) (hz : z ∈ closedBall c r) : (p i).eval z ≠ 0 :=
    fun h => hnonreal z hz (hiRoot z h)
  have hinv : DiffContOnCl ℂ (fun z => ((p i).eval z)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    exact (p i).differentiable.differentiableOn.inv hpnonzero
  have hbd (z : ℂ) (hz : z ∈ sphere c r) : ‖((p i).eval z)⁻¹‖ ≤ 2 / b := by
    have herr : ‖F z - (p i).eval z‖ < b / 4 := by
      simpa only [dist_eq_norm] using hiErr z (sphere_subset_closedBall hz)
    have htri : ‖F z‖ ≤ ‖F z - (p i).eval z‖ + ‖(p i).eval z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (F z - (p i).eval z) ((p i).eval z)
    have hnorm : b / 2 ≤ ‖(p i).eval z‖ := by linarith [hbmin z hz]
    rw [norm_inv, ← one_div]
    calc
      1 / ‖(p i).eval z‖ ≤ 1 / (b / 2) :=
        one_div_le_one_div_of_le (by positivity) hnorm
      _ = 2 / b := by ring
  have hcenter := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    0 hr hinv hbd
  have hcenter' : ‖((p i).eval c)⁻¹‖ ≤ 2 / b := by simpa using hcenter
  have hsmall : ‖(p i).eval c‖ < b / 4 := by
    have h := hiErr c (mem_closedBall_self hr.le)
    simpa only [hc, dist_eq_norm, zero_sub, norm_neg] using h
  have hpos : 0 < ‖(p i).eval c‖ :=
    norm_pos_iff.mpr (hpnonzero c (mem_closedBall_self hr.le))
  rw [norm_inv, ← one_div] at hcenter'
  have hlarge : 1 ≤ 2 / b * ‖(p i).eval c‖ := (div_le_iff₀ hpos).mp hcenter'
  have hstrict : 2 / b * ‖(p i).eval c‖ < 1 := by
    calc
      _ < 2 / b * (b / 4) := mul_lt_mul_of_pos_left hsmall (by positivity)
      _ < 1 := by field_simp [hb.ne']; linarith
  exact (not_lt_of_ge hlarge) hstrict

/-- The existing actual fixed-window estimate is uniform on every compact subset
of the entire plane, in its original theta source normalization. -/
private theorem sourceJensen_locallyUniform :
    TendstoLocallyUniformlyOn (fun n z => (sourcePolynomial n).eval z) sourceF atTop univ := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
  intro K _ hK
  obtain ⟨M, _, hM⟩ := hK.isBounded.exists_pos_norm_le
  let R : ℝ := max 1 M
  have hR : 1 ≤ R := le_max_left _ _
  rw [tendstoUniformlyOn_iff]
  intro e he
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * weightedNorm sourceA 2 R / e)
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn z hz
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right 1 N).trans hn)
  have herr : 2 / (n : ℝ) * weightedNorm sourceA 2 R < e := by
    have h := (div_lt_iff₀ he).mp (hN.trans_le hNn)
    rw [div_mul_eq_mul_div, div_lt_iff₀ hnR]
    linarith
  have hzR : ‖z‖ ≤ R := (hM z hz).trans (le_max_right _ _)
  rw [dist_eq_norm, norm_sub_rev]
  exact (source_uniform_approximation n hn1 R hR z hzR).trans_lt herr

/-- The existing theta coefficient source is the literal normalized xi-square
source, by the Fourier identity at both signs and reflection of xi. -/
theorem sourceF_eq_xiSquareSource : sourceF = xiSquareSource := by
  funext z
  let w := Complex.sqrt z
  let f : ℝ → ℂ := fun x => (sourceThetaKernel x : ℂ) * Complex.exp (Complex.I * w * (x : ℂ))
  let g : ℝ → ℂ := fun x => (sourceThetaKernel x : ℂ) * Complex.exp (Complex.I * (-w) * (x : ℂ))
  have hf : Integrable f := source_theta_fourier_integrable w
  have hg : Integrable g := source_theta_fourier_integrable (-w)
  have hfr : (∫ x : ℝ, f x) = xiReading ((1 / 2 : ℂ) + Complex.I * w) :=
    source_theta_fourier_eq_xi w
  have hgr : (∫ x : ℝ, g x) = xiReading ((1 / 2 : ℂ) + Complex.I * w) := by
    rw [show (∫ x : ℝ, g x) = xiReading ((1 / 2 : ℂ) + Complex.I * (-w)) from
      source_theta_fourier_eq_xi (-w)]
    rw [show (1 / 2 : ℂ) + Complex.I * (-w) =
        1 - ((1 / 2 : ℂ) + Complex.I * w) by ring, xi_reading_reflection]
  have hcenter : xiReading (1 / 2 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.zero_re] at hr
    linarith [source_theta_normalized.2.1]
  unfold sourceF cosineSquareTransform xiSquareSource
  calc
    _ = ∫ x : ℝ, (f x + g x) / (2 * xiReading (1 / 2)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [source_density_complex]
      have hcos := Complex.two_cos (w * (x : ℂ))
      have hcos' : 2 * Complex.cos (w * (x : ℂ)) =
          Complex.exp (Complex.I * w * (x : ℂ)) +
          Complex.exp (Complex.I * (-w) * (x : ℂ)) := by
        rw [show w * (x : ℂ) * Complex.I = Complex.I * w * (x : ℂ) by ring,
          show -(w * (x : ℂ)) * Complex.I = Complex.I * (-w) * (x : ℂ) by ring] at hcos
        exact hcos
      change (sourceThetaKernel x : ℂ) / xiReading (1 / 2) *
        Complex.cos (w * (x : ℂ)) = _
      rw [show Complex.cos (w * (x : ℂ)) =
        (Complex.exp (Complex.I * w * (x : ℂ)) +
          Complex.exp (Complex.I * (-w) * (x : ℂ))) / 2 by linear_combination hcos' / 2]
      simp only [f, g]
      field_simp [hcenter]
      <;> ring
    _ = ((∫ x : ℝ, f x) + ∫ x : ℝ, g x) / (2 * xiReading (1 / 2)) := by
      rw [integral_div, integral_add hf hg]
    _ = _ := by
      rw [hfr, hgr]
      change _ = xiReading ((1 / 2 : ℂ) + Complex.I * w) / _
      field_simp [hcenter]
      <;> ring

/-- If all reflected fixed-shift actual theta Jensen polynomials are real-rooted
eventually, their entire square source has no nonreal zero. -/
private theorem sourceF_allZerosReal_of_jensen
    (h : ∀ᶠ n : ℕ in atTop, AllRootsReal (sourcePolynomial n)) :
    ∀ z : ℂ, sourceF z = 0 → z.im = 0 :=
  allZerosReal_of_locallyUniform sourcePolynomial sourceF source_coefficients.2.1
    (by rw [source_at_zero]; exact one_ne_zero) sourceJensen_locallyUniform h

/-- The actual reflected fixed-shift Jensen tower implies standard RH.
The square-coordinate ambiguity is resolved by the unconditional absence of
zeta zeros on the real open critical interval. -/
private theorem rh_of_eventually_real_jensen
    (h : ∀ᶠ n : ℕ in atTop, AllRootsReal (sourcePolynomial n)) :
    RiemannHypothesis := by
  rw [rh_iff_nontrivial_zeros_on_line]
  intro s hs
  let w := -Complex.I * (s - 1/2)
  have hcoord : (1/2 : ℂ) + Complex.I * w = s := by
    dsimp [w]
    ring_nf
    norm_num [Complex.I_sq]
  have hz : sourceF (w ^ 2) = 0 := by
    rw [sourceF_eq_xiSquareSource, xi_square_source_entire_and_composition.2, hcoord,
      (xiReading_eq_zero_iff_nontrivial s).mpr hs, zero_div]
  have hw : (w ^ 2).im = 0 := sourceF_allZerosReal_of_jensen h _ hz
  have hwre : w.re = s.im := by simp [w, Complex.mul_re, Complex.sub_im]
  have hwim : w.im = 1/2 - s.re := by simp [w, Complex.mul_im, Complex.sub_re]
  have hsIm : s.im ≠ 0 := by
    intro hsi
    have hsr : s = (s.re : ℂ) := by apply Complex.ext <;> simp [hsi]
    have hnon := D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.riemannZeta_ne_zero_of_real_mem_Ioo
      s.re hs.2.1 hs.2.2
    apply hnon
    rw [← hsr]
    exact hs.1
  rw [pow_two, Complex.mul_im, hwre, hwim] at hw
  have hp : s.im * (1 / 2 - s.re) = 0 := by linarith
  have hc := (mul_eq_zero.mp hp).resolve_left hsIm
  linarith

/-- The actual positive-coefficient source polynomial and its reflected polynomial
have the same root-reality predicate. -/
theorem sourceJensen_real_iff_reflected (n : ℕ) :
    AllRootsReal (sourceJensenPolynomial n) ↔
      ∀ z : ℂ, (sourcePolynomial n).eval z = 0 → z.im = 0 := by
  have heq : sourcePolynomial n = (sourceJensenPolynomial n).comp (C (-1) * X) := by
    rw [sourcePolynomial, source_map]
  change AllRootsReal (sourceJensenPolynomial n) ↔ AllRootsReal (sourcePolynomial n)
  rw [heq]
  constructor
  · intro h z hz
    have h0 : (sourceJensenPolynomial n).eval (-z) = 0 := by
      simpa only [eval_comp, eval_mul, eval_C, eval_X, neg_one_mul] using hz
    have hi := h (-z) h0
    simpa using hi
  · intro h z hz
    have h0 : ((sourceJensenPolynomial n).comp (C (-1) * X)).eval (-z) = 0 := by
      simpa only [eval_comp, eval_mul, eval_C, eval_X, neg_one_mul, neg_neg] using hz
    have hi := h (-z) h0
    simpa using hi

theorem rh_of_actual_jensen_tower :
    let coordinate : ℂ → ℝ := Complex.re
    (∀ n : ℕ, 1 ≤ n → ∀ z : ℂ, (sourceJensenPolynomial n).eval z = 0 →
      coordinate ⟨z.im, z.re⟩ = 0) →
    ∀ (s : ℂ), riemannZeta s = 0 → (¬ ∃ m : ℕ, s = -2 * (m + 1)) →
      s ≠ 1 → coordinate s = (1 : ℝ) / 2 := by
  intro coordinate h
  change RiemannHypothesis
  exact rh_of_eventually_real_jensen ((eventually_ge_atTop 1).mono fun n hn =>
    (sourceJensen_real_iff_reflected n).mp (h n hn))

end D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
