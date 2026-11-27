/- GID: D5/S3/Fourier/Concentration/CauchyPairEnergy
   generality: I
   mirror-B: D5/B/S3/Fourier/Concentration/CauchyPairEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Localization of the Cauchy-smoothed energy gives a finite Lorentz pair-sum lower bound. -/

import D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Function.L2Space

/-! Energy of finite sums of translated Cauchy densities. -/

open MeasureTheory ProbabilityTheory Set
open scoped Interval ENNReal NNReal Convolution MeasureTheory ComplexConjugate

namespace D5.S3.Fourier.Concentration.CauchyPairEnergy

/-- The mass of a unit-scale Cauchy density in the buffered interval. -/
theorem cauchy_mass_buffer_interval {x₀ Y R : ℝ} (hle : -R ≤ Y + R) :
    (∫ x in Icc (-R) (Y + R), cauchyPDFReal x₀ 1 x) =
      Real.pi⁻¹ * (Real.arctan (Y + R - x₀) + Real.arctan (R + x₀)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  simp only [cauchyPDFReal_def, NNReal.coe_one, mul_one, one_pow]
  rw [intervalIntegral.integral_const_mul]
  simp_rw [add_comm ((_ - x₀) ^ 2) 1]
  rw [intervalIntegral.integral_comp_sub_right (f := fun x : ℝ => (1 + x ^ 2)⁻¹) x₀,
    integral_inv_one_add_sq, show -R - x₀ = -(R + x₀) by ring, Real.arctan_neg]
  ring

/-- Interval length controls the squared magnitude of an integral by its energy. -/
private theorem sq_norm_integral_le_energy {u v : ℝ} (huv : u ≤ v) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc u v)) :
    ‖∫ x in Icc u v, f x‖ ^ 2 ≤ (v - u) * ∫ x in Icc u v, ‖f x‖ ^ 2 := by
  let μ := volume.restrict (Icc u v)
  let g (x : ℝ) := ‖f x‖
  have hgc : ContinuousOn g (Icc u v) := hf.norm
  have hg2 : Integrable (fun x => g x ^ 2) μ :=
    (hgc.pow 2).integrableOn_compact isCompact_Icc
  have hgm : MemLp g (ENNReal.ofReal 2) μ := by
    simpa using (memLp_two_iff_integrable_sq
      (hgc.aestronglyMeasurable measurableSet_Icc)).2 hg2
  have h1m : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) μ := by
    have hcont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc u v) :=
      continuousOn_const
    have hint : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) μ :=
      (hcont.pow 2).integrableOn_compact isCompact_Icc
    simpa using (memLp_two_iff_integrable_sq
      (hcont.aestronglyMeasurable measurableSet_Icc)).2 hint
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x => show 0 ≤ g x from norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => (zero_le_one : (0 : ℝ) ≤ 1)) hgm h1m
  have hlen : (∫ _ : ℝ, (1 : ℝ) ∂μ) = v - u := by
    simp [μ, Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal, sub_nonneg.mpr huv]
  have hbound : (∫ x, g x ∂μ) ≤ Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (v - u) := by
    simpa only [one_pow, mul_one, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow, hlen] using hcs
  have henergy : 0 ≤ ∫ x, g x ^ 2 ∂μ :=
    integral_nonneg fun x => sq_nonneg (g x)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) ((norm_integral_le_integral_norm f).trans hbound) 2
  change ‖∫ x, f x ∂μ‖ ^ 2 ≤ (v - u) * ∫ x, g x ^ 2 ∂μ
  rw [mul_pow, Real.sq_sqrt henergy, Real.sq_sqrt (sub_nonneg.mpr huv),
    mul_comm] at hsquare
  exact hsquare

private lemma cauchy_one_continuous (c : ℝ) : Continuous (cauchyPDFReal c 1) := by
  have hden : Continuous (fun x : ℝ => (x - c) ^ 2 + 1) := by fun_prop
  have hc : Continuous (fun _ : ℝ => Real.pi⁻¹) := continuous_const
  have hf := hc.mul (hden.inv₀ fun x => by positivity)
  convert hf using 1
  ext x
  simp [cauchyPDFReal_def]

private lemma integral_cauchy_sum_buffer {J : Type*} (s : Finset J) (x : J → ℝ)
    (a : J → ℂ) {Y R : ℝ} (hx : ∀ j ∈ s, x j ∈ Icc 0 Y) (hR : 0 < R) :
    ‖∑ j ∈ s, a j‖ - (1 - Real.pi⁻¹ * (2 * Real.arctan R)) * ∑ j ∈ s, ‖a j‖ ≤
      ‖∫ u in Icc (-R) (Y + R), ∑ j ∈ s, a j * (cauchyPDFReal (x j) 1 u : ℂ)‖ := by
  let I := Icc (-R) (Y + R)
  let mass (j : J) := ∫ u in I, cauchyPDFReal (x j) 1 u
  let loss := 1 - Real.pi⁻¹ * (2 * Real.arctan R)
  have hInt : ∀ j ∈ s, IntegrableOn (fun u => a j * (cauchyPDFReal (x j) 1 u : ℂ)) I := by
    intro j _
    exact ((integrable_cauchyPDFReal (x j)).ofReal.const_mul (a j)).integrableOn
  have hsum : (∫ u in I, ∑ j ∈ s, a j * (cauchyPDFReal (x j) 1 u : ℂ)) =
      ∑ j ∈ s, a j * (mass j : ℂ) := by
    rw [integral_finsetSum s hInt]
    simp_rw [integral_const_mul, integral_complex_ofReal, mass]
  have hmass (j : J) : mass j ≤ 1 := by
    refine (setIntegral_le_integral (integrable_cauchyPDFReal (x j))
      (Filter.Eventually.of_forall fun u => (cauchyPDF_pos (x j) one_ne_zero u).le)).trans_eq ?_
    exact integral_cauchyPDFReal_eq_one (x j) one_ne_zero
  have hnorm (j : J) (hj : j ∈ s) : ‖a j - a j * (mass j : ℂ)‖ ≤ loss * ‖a j‖ := by
    have hcenter := hx j hj
    have hleft : R ≤ R + x j := by linarith [hcenter.1]
    have hright : R ≤ Y + R - x j := by linarith [hcenter.2]
    have hle : -R ≤ Y + R := by linarith [hcenter.1, hcenter.2]
    have hlow : 1 - loss ≤ mass j := by
      dsimp only [mass, I, loss]
      rw [cauchy_mass_buffer_interval hle, sub_sub_cancel]
      exact mul_le_mul_of_nonneg_left
        (by linarith [Real.arctan_mono hleft, Real.arctan_mono hright])
        (inv_nonneg.mpr Real.pi_pos.le)
    rw [← mul_one_sub, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (hmass j)), mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hdiff : ‖(∑ j ∈ s, a j) - ∑ j ∈ s, a j * (mass j : ℂ)‖ ≤
      loss * ∑ j ∈ s, ‖a j‖ := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact (norm_sum_le s _).trans (Finset.sum_le_sum hnorm)
  have h := norm_sub_norm_le (∑ j ∈ s, a j) (∑ j ∈ s, a j * (mass j : ℂ))
  rw [hsum]
  exact sub_le_comm.mp (h.trans hdiff)

open D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup

private lemma poissonKernel_eq_cauchyMeasure {γ : ℝ≥0} (hγ : γ ≠ 0) :
    poissonKernel γ = cauchyMeasure 0 γ := by
  let d : ℝ := 2 * (γ : ℝ)
  have hγpos : 0 < (γ : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hm : Measurable (d * ·) := measurable_const.mul measurable_id
  have hdensity (u : ℝ) : cauchyPDF 0 (1 / 2) u =
      ENNReal.ofReal d * cauchyPDF 0 γ (d * u) := by
    rw [cauchyPDF_def, cauchyPDF_def, ← ENNReal.ofReal_mul hd.le]
    congr 1
    rw [cauchyPDFReal_def', cauchyPDFReal_def']
    norm_num only [NNReal.coe_div, NNReal.coe_one, sub_zero, inv_div, div_one]
    rw [show d * u / (γ : ℝ) = u / (1 / 2) by
      dsimp [d]
      field_simp [hγpos.ne']
      <;> ring]
    dsimp [d]
    field_simp [hγpos.ne']
    <;> ring
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [poissonKernel, lintegral_map hf hm, halfCauchyMeasure,
    cauchyMeasure_of_scale_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0),
    cauchyMeasure_of_scale_ne_zero 0 hγ]
  change (∫⁻ x, (f ∘ (d * ·)) x ∂volume.withDensity (cauchyPDF 0 (1 / 2))) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_cauchyPDF _ _) (hf.comp hm)]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_cauchyPDF _ _) hf]
  calc
    (∫⁻ x, (cauchyPDF 0 (1 / 2) * (f ∘ (d * ·))) x) =
        ENNReal.ofReal d * ∫⁻ x, (cauchyPDF 0 γ * f) (d * x) := by
      change _ = ENNReal.ofReal d * ∫⁻ x, ((cauchyPDF 0 γ * f) ∘ (d * ·)) x
      rw [← lintegral_const_mul _ ((measurable_cauchyPDF _ _).mul hf |>.comp hm)]
      apply lintegral_congr
      intro u
      simp only [Pi.mul_apply, Function.comp_apply, hdensity u, mul_assoc]
    _ = ∫⁻ x, (cauchyPDF 0 γ * f) x ∂ENNReal.ofReal d • Measure.map (d * ·) volume := by
      rw [lintegral_smul_measure, lintegral_map ((measurable_cauchyPDF _ _).mul hf) hm]
      rfl
    _ = _ := by
      have hvol : ENNReal.ofReal d • Measure.map (d * ·) volume = volume := by
        simpa only [abs_of_pos hd] using Real.smul_map_volume_mul_left hd.ne'
      rw [hvol]

private lemma cauchy_one_norm_le (c u : ℝ) : ‖cauchyPDFReal c 1 u‖ ≤ Real.pi⁻¹ := by
  rw [Real.norm_of_nonneg (cauchyPDF_pos c one_ne_zero u).le, cauchyPDFReal_def]
  simpa only [NNReal.coe_one, mul_one, one_pow] using
    mul_le_of_le_one_right (inv_nonneg.mpr Real.pi_pos.le)
      (inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (u - c)] : 1 ≤ (u - c) ^ 2 + 1))

private lemma cauchy_one_convolution (z : ℝ) :
    (∫ u : ℝ, cauchyPDFReal 0 1 u * cauchyPDFReal 0 1 (z - u)) =
      cauchyPDFReal 0 2 z := by
  let p : ℝ → ℝ := cauchyPDFReal 0 1
  let g := p ⋆ p
  have hp : Integrable p := integrable_cauchyPDFReal _
  have hpC : Continuous p := cauchy_one_continuous _
  have hpb : BddAbove (range fun x => ‖p x‖) :=
    ⟨Real.pi⁻¹, by rintro _ ⟨x, rfl⟩; exact cauchy_one_norm_le _ _⟩
  have hgC : Continuous g :=
    hpb.continuous_convolution_right_of_integrable (ContinuousLinearMap.lsmul ℝ ℝ) hp hpC
  have hg_nonneg (x : ℝ) : 0 ≤ g x :=
    integral_nonneg (fun t => mul_nonneg (cauchyPDF_pos 0 one_ne_zero t).le
      (cauchyPDF_pos 0 one_ne_zero (x - t)).le)
  have hgDensity (x : ℝ) :
      (cauchyPDF 0 1 ⋆ₗ[volume] cauchyPDF 0 1) x = ENNReal.ofReal (g x) := by
    have hi : Integrable (fun u => p u * p (x - u)) :=
      hp.mul_bdd (c := Real.pi⁻¹) (hpC.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => cauchy_one_norm_le 0 (x - u))
    change _ = ENNReal.ofReal (∫ u, p u * p (x - u))
    rw [lconvolution_def, ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun u => mul_nonneg (cauchyPDF_pos 0 one_ne_zero u).le
        (cauchyPDF_pos 0 one_ne_zero (x - u)).le)]
    apply lintegral_congr
    intro u
    rw [neg_add_eq_sub, cauchyPDF_def, cauchyPDF_def,
      ENNReal.ofReal_mul (cauchyPDF_pos 0 one_ne_zero u).le]
  have h12 : cauchyMeasure 0 1 ∗ cauchyMeasure 0 1 = cauchyMeasure 0 2 := by
    simpa only [one_add_one_eq_two, poissonKernel_eq_cauchyMeasure one_ne_zero,
      poissonKernel_eq_cauchyMeasure (by norm_num : (2 : ℝ≥0) ≠ 0)]
      using poissonKernel_convolution (1 : ℝ≥0) 1
  have hmeasure : volume.withDensity (ENNReal.ofReal ∘ g) = volume.withDensity (cauchyPDF 0 2) := by
    rw [show ENNReal.ofReal ∘ g = cauchyPDF 0 1 ⋆ₗ[volume] cauchyPDF 0 1 from
      funext fun x => (hgDensity x).symm]
    rw [← conv_withDensity_eq_lconvolution (measurable_cauchyPDF _ _) (measurable_cauchyPDF _ _)]
    simpa only [cauchyMeasure_of_scale_ne_zero _ one_ne_zero,
      cauchyMeasure_of_scale_ne_zero _ (by norm_num : (2 : ℝ≥0) ≠ 0)] using h12
  have heq := (withDensity_eq_iff_of_sigmaFinite
    (ENNReal.continuous_ofReal.comp hgC).measurable.aemeasurable
    (measurable_cauchyPDF _ _).aemeasurable).mp hmeasure
  have hqC : Continuous (cauchyPDFReal 0 2) := by
    have hden : Continuous (fun x : ℝ => (x - 0) ^ 2 + 2 ^ 2) := by fun_prop
    have hc : Continuous (fun _ : ℝ => Real.pi⁻¹ * 2) := continuous_const
    have h := hc.mul (hden.inv₀ fun x => by positivity)
    convert h using 1
    ext x
    norm_num [cauchyPDFReal_def]
  have hreal : g =ᵐ[volume] cauchyPDFReal 0 2 := by
    filter_upwards [heq] with x hx
    have ht := congrArg ENNReal.toReal hx
    simpa [Function.comp_apply, cauchyPDF_def, ENNReal.toReal_ofReal, hg_nonneg x,
      (cauchyPDF_pos 0 (by norm_num : (2 : ℝ≥0) ≠ 0) x).le] using ht
  exact congrFun (Measure.eq_of_ae_eq hreal hgC hqC) z

private lemma cauchy_shift_inner (a b : ℝ) :
    (∫ u : ℝ, cauchyPDFReal a 1 u * cauchyPDFReal b 1 u) =
      (2 * Real.pi)⁻¹ * (4 / (4 + (a - b) ^ 2)) := by
  calc
    _ = ∫ u : ℝ, cauchyPDFReal 0 1 (u - a) *
        cauchyPDFReal 0 1 ((b - a) - (u - a)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [cauchyPDFReal_def, sub_zero]
      rw [show b - a - (u - a) = -(u - b) by ring, neg_sq]
    _ = ∫ u : ℝ, cauchyPDFReal 0 1 u * cauchyPDFReal 0 1 ((b - a) - u) :=
      integral_sub_right_eq_self (fun u : ℝ => cauchyPDFReal 0 1 u *
        cauchyPDFReal 0 1 ((b - a) - u)) a
    _ = cauchyPDFReal 0 2 (b - a) := cauchy_one_convolution _
    _ = _ := by
      rw [cauchyPDFReal_def]
      norm_num only [NNReal.coe_ofNat, sub_zero, Nat.ofNat_pos, pow_two]
      rw [show (b - a) * (b - a) = (a - b) * (a - b) by ring]
      simp only [div_eq_mul_inv, add_comm]
      field_simp [Real.pi_ne_zero]
      norm_num

private lemma cauchy_sum_square {J : Type*} (s : Finset J) (x : J → ℝ)
    (a : J → ℂ) (u : ℝ) :
    ‖∑ i ∈ s, a i * (cauchyPDFReal (x i) 1 u : ℂ)‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re *
        (cauchyPDFReal (x i) 1 u * cauchyPDFReal (x j) 1 u) := by
  let p (i : J) := cauchyPDFReal (x i) 1 u
  let q (i : J) := a i * (p i : ℂ)
  change ‖∑ i ∈ s, q i‖ ^ 2 =
    ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re * (p i * p j)
  rw [← Complex.normSq_eq_norm_sq]
  have h (z : ℂ) : Complex.normSq z = (z * conj z).re := by
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [h, map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hprod : q i * conj (q j) =
      ((p i * p j : ℝ) : ℂ) * (a i * conj (a j)) := by
    simp only [q, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  rw [hprod, Complex.re_ofReal_mul, mul_comm]

private lemma integrable_cauchy_pair (c d : ℝ) :
    Integrable (fun u => cauchyPDFReal c 1 u * cauchyPDFReal d 1 u) :=
  (integrable_cauchyPDFReal c).mul_bdd (c := Real.pi⁻¹)
    (cauchy_one_continuous d).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => cauchy_one_norm_le d u)

private lemma cauchy_pair_energy {J : Type*} (s : Finset J) (x : J → ℝ)
    (a : J → ℂ) :
    (∫ u : ℝ, ‖∑ i ∈ s, a i * (cauchyPDFReal (x i) 1 u : ℂ)‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re *
        (4 / (4 + (x i - x j) ^ 2)) := by
  have hi (i j : J) : Integrable (fun u =>
      (a i * conj (a j)).re * (cauchyPDFReal (x i) 1 u * cauchyPDFReal (x j) 1 u)) :=
    (integrable_cauchy_pair (x i) (x j)).const_mul _
  simp_rw [cauchy_sum_square s x a]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum s (fun j _ => hi i j))]
  simp_rw [integral_finsetSum s (fun j _ => hi _ j), integral_const_mul,
    cauchy_shift_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Lorentz pair sum controls the total coefficient mass after the Cauchy tail loss. -/
theorem lorentz_pair_lower_bound {J : Type*} (s : Finset J)
    (x : J → ℝ) (a : J → ℂ) {Y R : ℝ}
    (hx : ∀ j ∈ s, x j ∈ Icc 0 Y) (hR : 0 < R) :
    (2 * Real.pi) / (Y + 2 * R) *
      max (‖∑ j ∈ s, a j‖ - (1 - Real.pi⁻¹ * (2 * Real.arctan R)) * ∑ j ∈ s, ‖a j‖) 0 ^ 2 ≤
        ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re * (4 / (4 + (x i - x j) ^ 2)) := by
  by_cases hs : s.Nonempty
  · obtain ⟨j, hj⟩ := hs
    have hY : 0 ≤ Y := (hx j hj).1.trans (hx j hj).2
    let f (u : ℝ) := ∑ j ∈ s, a j * (cauchyPDFReal (x j) 1 u : ℂ)
    have hf : Continuous f := by
      apply continuous_finsetSum s
      intro j _
      exact continuous_const.mul (Complex.continuous_ofReal.comp (cauchy_one_continuous _))
    have hfi : Integrable (fun u => ‖f u‖ ^ 2) := by
      simp_rw [f, cauchy_sum_square s x a]
      exact integrable_finsetSum s fun i _ => integrable_finsetSum s fun j _ =>
        (integrable_cauchy_pair (x i) (x j)).const_mul _
    have hdist : 0 < Y + 2 * R := by linarith
    have hlen : Y + R - -R = Y + 2 * R := by ring
    have hbuffer := max_le (integral_cauchy_sum_buffer s x a hx hR) (norm_nonneg _)
    have hsquare := pow_le_pow_left₀ (le_max_right _ _) hbuffer 2
    have hloc := sq_norm_integral_le_energy (u := -R) (v := Y + R)
      (by linarith) hf.continuousOn
    rw [hlen] at hloc
    have hwhole := setIntegral_le_integral (s := Icc (-R) (Y + R)) hfi
      (Filter.Eventually.of_forall fun u => sq_nonneg ‖f u‖)
    have hbound := hsquare.trans (hloc.trans (mul_le_mul_of_nonneg_left hwhole hdist.le))
    dsimp only [f] at hbound
    rw [cauchy_pair_energy] at hbound
    have h := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 2 * Real.pi by positivity)
    rw [div_mul_eq_mul_div, div_le_iff₀ hdist]
    convert h using 1
    field_simp [Real.pi_ne_zero]
    <;> ring
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end D5.S3.Fourier.Concentration.CauchyPairEnergy
