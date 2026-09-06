/- GID: D5/S3/Fourier/InfiniteSincProduct
   generality: I
   mirror-B: D5/B/S3/Fourier/InfiniteSincProduct
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct dyadic uniform-interval data whose sinc product is nonzero off the real axis. -/

/- Library-search audit trail (2026-09-06):
   * D5 searches for `sinc`, infinite products, `tprod`, `HasProd`,
     `Multipliable`, uniform densities, convolution, and nonreal Fourier
     nonvanishing found no equivalent declaration. The frozen Paley-Wiener
     and finite interpolation results do not control an infinite product.
   * Pinned Mathlib provides `tprod_one_add_ne_zero_of_summable`,
     `Summable.hasProdUniformlyOn_nat_one_add`,
     `Complex.exp_sub_sum_range_isBigO_pow`, and
     `Complex.sin_ne_zero_iff`. Mathlib defines only `Real.sinc`, so the
     removable complex extension is defined below.
   * Credential-free GitHub repository search for `Lean4 sinc infinite
     product`, `Lean4 "infinite product"`, and `Lean theorem prover sinc`
     returned no repository hit. Authenticated code-level third-party search
     was unavailable and is recorded as ASSUMED-UNVERIFIED.
-/

import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace D5.S3.Fourier.InfiniteSincProduct

open Asymptotics Filter MeasureTheory Set Topology
open scoped Interval

noncomputable section

/-- The removable complex extension of `sin z / z`. -/
noncomputable def complexSinc : ℂ → ℂ :=
  Function.update (fun z : ℂ ↦ Complex.sin z / z) 0 1

@[simp] theorem complexSinc_zero : complexSinc 0 = 1 := by
  simp [complexSinc]

theorem complexSinc_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    complexSinc z = Complex.sin z / z := by
  simp [complexSinc, hz]

theorem continuous_complexSinc : Continuous complexSinc := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    simpa [complexSinc] using (Complex.hasDerivAt_sin 0).continuousAt_div
  · rw [complexSinc, continuousAt_update_of_ne hz]
    exact Complex.continuous_sin.continuousAt.div continuousAt_id hz

private lemma complexSinc_sub_one_isBigO_sq :
    (fun z : ℂ ↦ complexSinc z - 1) =O[nhds 0] (fun z : ℂ ↦ z ^ 2) := by
  let P : ℂ → ℂ := fun w ↦ ∑ i ∈ Finset.range 3, w ^ i / (i.factorial : ℂ)
  have hP (w : ℂ) : P w = 1 + w + w ^ 2 / 2 := by
    norm_num [P, Finset.sum_range_succ]
    <;> ring
  have hminus₀ := (Complex.exp_sub_sum_range_isBigO_pow 3).comp_tendsto
    (show Tendsto (fun z : ℂ ↦ -z * Complex.I) (nhds 0) (nhds 0) by
      have hz : Tendsto (fun z : ℂ ↦ z) (nhds 0) (nhds 0) := tendsto_id
      have hI : Tendsto (fun _ : ℂ ↦ Complex.I) (nhds 0) (nhds Complex.I) :=
        tendsto_const_nhds
      simpa using hz.neg.mul hI)
  have hplus₀ := (Complex.exp_sub_sum_range_isBigO_pow 3).comp_tendsto
    (show Tendsto (fun z : ℂ ↦ z * Complex.I) (nhds 0) (nhds 0) by
      have hz : Tendsto (fun z : ℂ ↦ z) (nhds 0) (nhds 0) := tendsto_id
      have hI : Tendsto (fun _ : ℂ ↦ Complex.I) (nhds 0) (nhds Complex.I) :=
        tendsto_const_nhds
      simpa using hz.mul hI)
  have hminusPow : (fun z : ℂ ↦ (-z * Complex.I) ^ 3) =O[nhds 0]
      (fun z : ℂ ↦ z ^ 3) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)
    simp [norm_pow]
  have hplusPow : (fun z : ℂ ↦ (z * Complex.I) ^ 3) =O[nhds 0]
      (fun z : ℂ ↦ z ^ 3) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z ↦ ?_)
    simp [norm_pow]
  have hminus : (fun z : ℂ ↦ Complex.exp (-z * Complex.I) - P (-z * Complex.I))
      =O[nhds 0] (fun z : ℂ ↦ z ^ 3) := by
    simpa [P, Function.comp_def] using hminus₀.trans hminusPow
  have hplus : (fun z : ℂ ↦ Complex.exp (z * Complex.I) - P (z * Complex.I))
      =O[nhds 0] (fun z : ℂ ↦ z ^ 3) := by
    simpa [P, Function.comp_def] using hplus₀.trans hplusPow
  have hsin : (fun z : ℂ ↦ Complex.sin z - z) =O[nhds 0] (fun z : ℂ ↦ z ^ 3) := by
    refine ((hminus.sub hplus).const_mul_left (Complex.I / 2)).congr_left fun z ↦ ?_
    rw [hP, hP]
    simp only [Complex.sin]
    ring_nf
    simp [sub_eq_add_neg]
  rw [isBigO_iff] at hsin
  rw [isBigO_iff]
  obtain ⟨C, hC⟩ := hsin
  refine ⟨C, hC.mono fun z hz ↦ ?_⟩
  by_cases hz₀ : z = 0
  · subst z
    simp
  · have hzNe : z ≠ 0 := by exact hz₀
    rw [complexSinc_of_ne_zero hzNe, div_sub_one hzNe, norm_div,
      div_le_iff₀ (norm_pos_iff.mpr hzNe)]
    calc
      ‖Complex.sin z - z‖ ≤ C * ‖z ^ 3‖ := hz
      _ = C * ‖z ^ 2‖ * ‖z‖ := by
        rw [show z ^ 3 = z ^ 2 * z by ring, norm_mul]
        ring

/-- The half-width of the `n`th uniform interval; `n = 0` represents the
atom's index `j = 1`. -/
noncomputable def dyadicHalfWidth (ell : ℝ) (n : ℕ) : ℝ :=
  ell / 2 ^ (n + 2)

/-- The density of the uniform probability law on `[-a, a]`. -/
noncomputable def uniformIntervalDensity (a : ℝ) : ℝ → ℝ :=
  Set.Icc (-a) a |>.indicator (fun _ ↦ (2 * a)⁻¹)

theorem uniformIntervalDensity_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 ≤ uniformIntervalDensity a x := by
  by_cases hx : x ∈ Set.Icc (-a) a
  · simp [uniformIntervalDensity, hx, ha.le]
  · simp [uniformIntervalDensity, hx]

theorem uniformIntervalDensity_even (a x : ℝ) :
    uniformIntervalDensity a (-x) = uniformIntervalDensity a x := by
  have hmem : -x ∈ Set.Icc (-a) a ↔ x ∈ Set.Icc (-a) a := by
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ Set.Icc (-a) a
  · rw [uniformIntervalDensity, Set.indicator_of_mem hx,
      Set.indicator_of_mem (hmem.mpr hx)]
  · rw [uniformIntervalDensity, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (not_congr hmem |>.mpr hx)]

theorem uniformIntervalDensity_integrable (a : ℝ) :
    Integrable (uniformIntervalDensity a) := by
  apply IntegrableOn.integrable_indicator
  · exact integrableOn_const measure_Icc_lt_top.ne
  · exact measurableSet_Icc

theorem integral_uniformIntervalDensity {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, uniformIntervalDensity a x = 1 := by
  simp [uniformIntervalDensity, Real.volume_Icc, ha.le, ENNReal.toReal_ofReal] <;>
    norm_num <;> field_simp <;> norm_num

private lemma tendsto_width_zero {a : ℕ → ℝ}
    (hsq : Summable (fun n ↦ a n ^ 2)) : Tendsto a atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq.tendsto_atTop_zero
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using hsqrt

private lemma summable_norm_complexSinc_sub_one {a : ℕ → ℝ}
    (hsq : Summable (fun n ↦ a n ^ 2)) (z : ℂ) :
    Summable (fun n ↦ ‖complexSinc ((a n : ℂ) * z) - 1‖) := by
  have ha₀ : Tendsto (fun n ↦ (a n : ℂ)) atTop (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_width_zero hsq)
  have hw₀ : Tendsto (fun n ↦ (a n : ℂ) * z) atTop (nhds 0) := by
    simpa using ha₀.mul_const z
  have hO := complexSinc_sub_one_isBigO_sq.comp_tendsto hw₀
  have hright : Summable (fun n ↦ ‖((a n : ℂ) * z) ^ 2‖) := by
    refine (hsq.mul_left (‖z‖ ^ 2)).congr fun n ↦ ?_
    simp [norm_pow, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
  exact summable_of_isBigO_nat hright hO.norm_norm

private lemma hasProdUniformlyOn_complexSinc {a : ℕ → ℝ}
    (hsq : Summable (fun n ↦ a n ^ 2)) {K : Set ℂ} (hK : IsCompact K) :
    HasProdUniformlyOn (fun n z ↦ complexSinc ((a n : ℂ) * z))
      (fun z ↦ ∏' n, complexSinc ((a n : ℂ) * z)) K := by
  obtain ⟨C, hC⟩ := isBigO_iff.mp complexSinc_sub_one_isBigO_sq
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  have ha₀ : Tendsto (fun n ↦ |a n|) atTop (nhds 0) := by
    simpa [Real.norm_eq_abs] using
      (tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_width_zero hsq))
  have hset : {w : ℂ | ‖complexSinc w - 1‖ ≤ C * ‖w ^ 2‖} ∈ nhds 0 := hC
  obtain ⟨eps, heps, heps_sub⟩ := Metric.mem_nhds_iff.mp hset
  have hscaled₀ : Tendsto (fun n ↦ |a n| * R) atTop (nhds 0) := by
    simpa using ha₀.mul_const R
  have hsmall : ∀ᶠ n in atTop, |a n| * R < eps :=
    hscaled₀.eventually (isOpen_Iio.mem_nhds heps)
  let u : ℕ → ℝ := fun n ↦ (|C| * R ^ 2) * a n ^ 2
  have hu : Summable u := hsq.mul_left (|C| * R ^ 2)
  have hbound : ∀ᶠ n in atTop, ∀ z ∈ K,
      ‖complexSinc ((a n : ℂ) * z) - 1‖ ≤ u n := by
    filter_upwards [hsmall] with n hn z hz
    have hwlt : ‖(a n : ℂ) * z‖ < eps := by
      calc
        ‖(a n : ℂ) * z‖ = |a n| * ‖z‖ := by simp [Real.norm_eq_abs]
        _ ≤ |a n| * R := mul_le_mul_of_nonneg_left (hR z hz) (abs_nonneg _)
        _ < eps := hn
    have hwmem : (a n : ℂ) * z ∈ Metric.ball 0 eps := by
      simpa [Metric.mem_ball, dist_zero_right] using hwlt
    have hlocal := heps_sub hwmem
    calc
      ‖complexSinc ((a n : ℂ) * z) - 1‖ ≤
          C * ‖((a n : ℂ) * z) ^ 2‖ := hlocal
      _ ≤ |C| * ‖((a n : ℂ) * z) ^ 2‖ := by
        gcongr
        exact le_abs_self C
      _ = |C| * a n ^ 2 * ‖z‖ ^ 2 := by
        simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [mul_pow, sq_abs]
        ring
      _ ≤ |C| * a n ^ 2 * R ^ 2 := by
        gcongr
        exact hR z hz
      _ = u n := by
        simp [u]
        ring
  have hcts : ∀ n, ContinuousOn (fun z : ℂ ↦
      complexSinc ((a n : ℂ) * z) - 1) K := by
    intro n
    exact ((continuous_complexSinc.comp (continuous_const.mul continuous_id)).sub
      continuous_const).continuousOn
  simpa using
    (Summable.hasProdUniformlyOn_nat_one_add hK hu hbound hcts)

private lemma complexSinc_ne_zero_of_im_ne_zero {a : ℝ} (ha : a ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) : complexSinc ((a : ℂ) * z) ≠ 0 := by
  have haw : (a : ℂ) * z ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) (by
    intro hz₀
    apply hz
    simp [hz₀])
  rw [complexSinc_of_ne_zero haw]
  refine div_ne_zero (Complex.sin_ne_zero_iff.mpr fun k hk ↦ ?_) haw
  have him : a * z.im = 0 := by
    calc
      a * z.im = (((a : ℂ) * z).im) := by simp
      _ = (((k : ℂ) * (Real.pi : ℂ)).im) := congrArg Complex.im hk
      _ = 0 := by simp
  exact hz (mul_eq_zero.mp him |>.resolve_left ha)

/-- Square summability of real interval half-widths gives compact-uniform
convergence of the sinc product; if no width vanishes, its value cannot vanish
away from the real axis. -/
theorem infinite_sinc_product_ne_zero_off_real (a : ℕ → ℝ)
    (ha : ∀ n, a n ≠ 0) (hsq : Summable (fun n ↦ a n ^ 2)) :
    (∀ K : Set ℂ, IsCompact K →
      HasProdUniformlyOn (fun n z ↦ complexSinc ((a n : ℂ) * z))
        (fun z ↦ ∏' n, complexSinc ((a n : ℂ) * z)) K) ∧
    ∀ z : ℂ, z.im ≠ 0 → ∏' n, complexSinc ((a n : ℂ) * z) ≠ 0 := by
  constructor
  · intro K hK
    exact hasProdUniformlyOn_complexSinc hsq hK
  · intro z hz
    have hsum := summable_norm_complexSinc_sub_one hsq z
    have hnonzero (n : ℕ) :
        1 + (complexSinc ((a n : ℂ) * z) - 1) ≠ 0 := by
      simpa using complexSinc_ne_zero_of_im_ne_zero (ha n) hz
    simpa using
      (tprod_one_add_ne_zero_of_summable hnonzero hsum)

private lemma summable_sq_dyadicHalfWidth (ell : ℝ) :
    Summable (fun n ↦ dyadicHalfWidth ell n ^ 2) := by
  have hgeom : Summable (fun n : ℕ ↦ ((1 : ℝ) / 4) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  refine (hgeom.mul_left (ell ^ 2 / 16)).congr fun n ↦ ?_
  have hpow : (4 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n * 2) := by
    rw [show (4 : ℝ)⁻¹ = ((2 : ℝ)⁻¹) ^ 2 by norm_num, ← pow_mul,
      Nat.mul_comm]
  simp [dyadicHalfWidth, pow_add, div_pow, hpow]
  ring

private lemma tsum_dyadicHalfWidth (ell : ℝ) :
    ∑' n, dyadicHalfWidth ell n = ell / 2 := by
  have hfun : (fun n ↦ dyadicHalfWidth ell n) =
      (fun n : ℕ ↦ ell / 2 / 2 / 2 ^ n) := by
    funext n
    simp [dyadicHalfWidth, pow_add]
    ring
  rw [hfun]
  exact tsum_geometric_two' (ell / 2)

/-- The explicit dyadic uniform-interval convolution data have total
half-width `ell / 2`; their Fourier sinc factors converge uniformly on every
complex compact set and their product is nonzero at every nonreal point. -/
theorem dyadic_uniform_convolution_product_ne_zero_off_real (ell : ℝ) (hell : 0 < ell) :
    (∀ n,
      0 < dyadicHalfWidth ell n ∧
      (∀ x, 0 ≤ uniformIntervalDensity (dyadicHalfWidth ell n) x) ∧
      (∀ x, uniformIntervalDensity (dyadicHalfWidth ell n) (-x) =
        uniformIntervalDensity (dyadicHalfWidth ell n) x) ∧
      Integrable (uniformIntervalDensity (dyadicHalfWidth ell n)) ∧
      ∫ x : ℝ, uniformIntervalDensity (dyadicHalfWidth ell n) x = 1) ∧
    (∑' n, dyadicHalfWidth ell n) = ell / 2 ∧
    (∀ K : Set ℂ, IsCompact K →
      HasProdUniformlyOn
        (fun n z ↦ complexSinc ((dyadicHalfWidth ell n : ℝ) * z))
        (fun z ↦ ∏' n, complexSinc ((dyadicHalfWidth ell n : ℝ) * z)) K) ∧
    ∀ z : ℂ, z.im ≠ 0 →
      ∏' n, complexSinc ((dyadicHalfWidth ell n : ℝ) * z) ≠ 0 := by
  have hwidthPos (n : ℕ) : 0 < dyadicHalfWidth ell n := by
    simp [dyadicHalfWidth]
    positivity
  have hwitness := infinite_sinc_product_ne_zero_off_real
    (dyadicHalfWidth ell) (fun n ↦ (hwidthPos n).ne') (summable_sq_dyadicHalfWidth ell)
  refine ⟨?_, tsum_dyadicHalfWidth ell, hwitness.1, hwitness.2⟩
  intro n
  exact ⟨hwidthPos n,
    uniformIntervalDensity_nonneg (hwidthPos n),
    uniformIntervalDensity_even _,
    uniformIntervalDensity_integrable _,
    integral_uniformIntervalDensity (hwidthPos n)⟩

#print axioms dyadic_uniform_convolution_product_ne_zero_off_real

end

end D5.S3.Fourier.InfiniteSincProduct
