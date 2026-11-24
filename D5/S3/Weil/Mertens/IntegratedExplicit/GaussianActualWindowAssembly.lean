import D5.S3.Weil.Mertens.IntegratedExplicit.ActualGaussianLeadingOscillation
import D5.S3.Weil.Mertens.IntegratedExplicit.GaussianSpectrumIntegral

/-! Approximation of the positive-log-scale Gaussian average by its explicit
spectrum, with an exponentially small lower-end correction. -/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualData)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)

namespace GaussianActualWindowAssembly

open TriangularPolePreservation GaussianSpectrumIntegral ActualGaussianLeadingOscillation

def coefficientMass : ℝ := ∑' n : ℕ, ‖distinctCoeff n‖

def zeroSeries (t : ℝ) : ℂ :=
  ∑' n : ℕ, distinctCoeff n * Complex.exp ((t : ℂ) * actualData.zero n)

def average (T : ℝ) (V : NNReal) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (logHinge t : ℂ) ∂gaussianReal T V

private theorem bound_series (t : ℝ) :
    ‖zeroSeries t‖ ≤ coefficientMass * Real.exp (max t 0) := by
  let f (n : ℕ) := distinctCoeff n * Complex.exp ((t : ℂ) * actualData.zero n)
  have h (n : ℕ) : ‖f n‖ ≤ ‖distinctCoeff n‖ * Real.exp (max t 0) := by
    rw [show ‖f n‖ = ‖distinctCoeff n‖ * Real.exp (t * (actualData.zero n).re) by
      simp only [f, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hz := (actualData.zero_isNontrivial n).2
    rcases le_total 0 t with ht | ht
    · exact (mul_le_of_le_one_right ht hz.2.le).trans (le_max_left _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg ht hz.1.le).trans (le_max_right _ _)
  have hs := distinctCoeff_summable.mul_right (Real.exp (max t 0))
  have hf := Summable.of_nonneg_of_le (fun n => norm_nonneg (f n)) h hs
  exact (norm_tsum_le_tsum_norm hf).trans
   ((hf.tsum_le_tsum h hs).trans_eq (distinctCoeff_summable.tsum_mul_right _))

theorem logHinge_growth {t : ℝ} (ht : 0 < t) :
    |logHinge t| ≤ (coefficientMass + 6) * Real.exp t := by
  have hspec := (logHinge_distinct_spectrum ht).tsum_eq
  change zeroSeries t = ((logHinge t - trivialCorrection t : ℝ) : ℂ) at hspec
  have hc := trivialCorrection_norm_le ht.le
  have hs := bound_series t
  rw [hspec, Complex.norm_real, Real.norm_eq_abs, max_eq_left ht.le] at hs
  have he := Real.exp_le_exp.mpr (show -2 * t ≤ t by linarith)
  rcases abs_le.mp hs with ⟨hslo, hshi⟩
  rcases abs_le.mp hc with ⟨hclo, hchi⟩
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ (6 : ℝ) by norm_num)
  apply abs_le.mpr
  constructor <;> linarith only [hslo,hshi,hclo,hchi,he']

private theorem zeroSeries_measurable : Measurable zeroSeries := by
  unfold zeroSeries
  apply Measurable.tsum
  intro n
  exact (by fun_prop : Continuous
    (fun t : ℝ => distinctCoeff n * Complex.exp ((t : ℂ) * actualData.zero n))).measurable

private theorem logHinge_continuous : Continuous logHinge := by
  rw [show logHinge = fun t => U (4 * Real.exp t) - 3 * U (2 * Real.exp t) + 2 * U (Real.exp t)
    from funext logHinge_eq]
  have h4 : ∀ t : ℝ, U (4 * Real.exp t) = U (Real.exp (t + 2 * Real.log 2)) := by
    intro t
    have hf : Real.exp (2 * Real.log 2) = 4 := by
      rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [Real.exp_add, hf, mul_comm]
  have h2 : ∀ t : ℝ, U (2 * Real.exp t) = U (Real.exp (t + Real.log 2)) := by
    intro t
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm]
  simp_rw [h4,h2]
  have h := D5.S3.Weil.Mertens.IntegratedExplicit.U_exp_continuous
  exact ((h.comp (continuous_id.add continuous_const)).sub
    (continuous_const.mul (h.comp (continuous_id.add continuous_const)))).add
    (continuous_const.mul h)

theorem average_spectrum_error {v T : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1 / 4) (hT : 0 ≤ T) :
    let V : NNReal := ⟨v * T, mul_nonneg hv hT⟩
    ‖average T V - ∑' n : ℕ, distinctCoeff n *
      Complex.exp ((T : ℂ) * mode v n)‖ ≤
        (6 + coefficientMass) * Real.exp (-T / 2) := by
  dsimp only
  let V : NNReal := ⟨v * T, mul_nonneg hv hT⟩
  let μ := gaussianReal T V
  let H := (Ioi (0 : ℝ)).indicator (fun t => (logHinge t : ℂ))
  let D := fun t : ℝ => H t - zeroSeries t
  let major := fun t : ℝ => 6 * Real.exp (-2 * t) + coefficientMass * Real.exp (-t)
  have hmass : 0 ≤ coefficientMass := tsum_nonneg (fun _ => norm_nonneg _)
  have hD (t : ℝ) : ‖D t‖ ≤ major t := by
    by_cases ht : 0 < t
    · have hspec := (logHinge_distinct_spectrum ht).tsum_eq
      change zeroSeries t = ((logHinge t - trivialCorrection t : ℝ) : ℂ) at hspec
      rw [show D t = (trivialCorrection t : ℂ) by
        dsimp [D,H]
        rw [indicator_of_mem (show t ∈ Ioi 0 from ht), hspec]
        push_cast
        ring,
        Complex.norm_real, Real.norm_eq_abs]
      exact (trivialCorrection_norm_le ht.le).trans (by
        dsimp [major]
        linarith [mul_nonneg hmass (Real.exp_nonneg (-t))])
    · have ht' := le_of_not_gt ht
      have hb := bound_series t
      rw [max_eq_right ht', Real.exp_zero, mul_one] at hb
      have hle : 1 ≤ Real.exp (-t) := Real.one_le_exp (neg_nonneg.mpr ht')
      dsimp [D, H, major]
      rw [indicator_of_notMem (show t ∉ Ioi 0 from ht), zero_sub, norm_neg]
      nlinarith [mul_le_mul_of_nonneg_left hle hmass, Real.exp_nonneg (-2 * t)]
  have hmajor : Integrable major μ := by
    have h1 : Integrable (fun t : ℝ => Real.exp (-t)) μ := by
      simpa only [neg_mul, one_mul] using
        (integrable_exp_mul_gaussianReal (μ := T) (v := V) (-1))
    exact ((integrable_exp_mul_gaussianReal (μ := T) (v := V) (-2)).const_mul 6).add
      (h1.const_mul _)
  have hF : Integrable zeroSeries μ := by
    have hExp : Integrable (fun t : ℝ => 1 + Real.exp t) μ := by
      have hh : Integrable Real.exp μ := by
        simpa only [one_mul] using (integrable_exp_mul_gaussianReal (μ := T) (v := V) 1)
      exact (integrable_const _).add hh
    apply (hExp.const_mul coefficientMass).mono' zeroSeries_measurable.aestronglyMeasurable
    filter_upwards with t
    refine (bound_series t).trans (mul_le_mul_of_nonneg_left ?_ hmass)
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht]
      linarith
    · rw [max_eq_right ht, Real.exp_zero]
      linarith [Real.exp_nonneg t]
  have hDint : Integrable D μ := hmajor.mono'
    (((Complex.continuous_ofReal.comp logHinge_continuous).measurable.indicator
      measurableSet_Ioi).sub zeroSeries_measurable).aestronglyMeasurable
    (ae_of_all _ hD)
  have hH : Integrable H μ := by
    convert hDint.add hF using 1
    ext t
    dsimp [D]
    ring
  have hspec := hasSum_gaussian_spectrum
    (z := actualData.zero) (a := distinctCoeff)
    (fun n => ⟨(actualData.zero_isNontrivial n).2.1.le, (actualData.zero_isNontrivial n).2.2.le⟩)
    distinctCoeff_summable T V
  have hform (n : ℕ) : actualData.zero n * (T : ℂ) + (V : ℂ) * (actualData.zero n) ^ 2 / 2 =
      (T : ℂ) * mode v n := by
    change _ + ((v * T : ℝ) : ℂ) * _ / 2 = _
    push_cast [mode, GaussianLeadingSpectrum.exponent]
    ring
  simp_rw [hform] at hspec
  have hEq : (∫ t, D t ∂μ) = average T V - ∑' n : ℕ,
      distinctCoeff n * Complex.exp ((T : ℂ) * mode v n) := by
    rw [show (∫ t, D t ∂μ) = (∫ t, H t ∂μ) - ∫ t, zeroSeries t ∂μ from integral_sub hH hF,
      show (∫ t, H t ∂μ) = average T V from integral_indicator measurableSet_Ioi,
      hspec.tsum_eq]
    unfold μ zeroSeries
    simp only [mul_comm]
  rw [← hEq]
  refine (norm_integral_le_of_norm_le hmajor (ae_of_all _ hD)).trans ?_
  have hre : (∫ t, major t ∂μ) = 6 * mgf (fun t : ℝ => t) μ (-2) +
      coefficientMass * mgf (fun t : ℝ => t) μ (-1) := by
    unfold major mgf
    simp only [neg_mul, one_mul]
    have h1 : Integrable (fun t : ℝ => Real.exp (-t)) μ := by
      simpa only [neg_mul, one_mul] using
        (integrable_exp_mul_gaussianReal (μ := T) (v := V) (-1))
    have h2 : Integrable (fun t : ℝ => Real.exp (-(2 * t))) μ := by
      simpa only [neg_mul] using
        (integrable_exp_mul_gaussianReal (μ := T) (v := V) (-2))
    rw [integral_add (h2.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul]
  rw [hre]
  change 6 * mgf (fun t : ℝ => t) (gaussianReal T V) (-2) +
    coefficientMass * mgf (fun t : ℝ => t) (gaussianReal T V) (-1) ≤ _
  rw [mgf_fun_id_gaussianReal, add_mul]
  have hvT := mul_le_mul_of_nonneg_right hv' hT
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hmass)
  · change T * (-2) + (v * T) * (-2) ^ 2 / 2 ≤ -T / 2
    nlinarith only [hvT, hT]
  · change T * (-1) + (v * T) * (-1) ^ 2 / 2 ≤ -T / 2
    nlinarith only [hvT, hT]

private theorem normalized_average_error {v topScore T : ℝ}
    (hv : 0 ≤ v) (hv' : v ≤ 1 / 4) (hT : 0 ≤ T) (hscore : 0 ≤ topScore) :
    let V : NNReal := ⟨v * T, mul_nonneg hv hT⟩
    ‖(Real.exp (-topScore * T) : ℂ) * average T V - normalized v topScore T‖ ≤
      (6 + coefficientMass) * Real.exp (-T / 2) := by
  dsimp only
  let V : NNReal := ⟨v * T, mul_nonneg hv hT⟩
  let D := ∑' n : ℕ, distinctCoeff n * Complex.exp ((T : ℂ) * mode v n)
  have hscale : normalized v topScore T = (Real.exp (-topScore * T) : ℂ) * D := by
    unfold normalized D
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [Complex.ofReal_exp]
    push_cast
    rw [show (T : ℂ) * (mode v n - (topScore : ℂ)) =
      -(topScore : ℂ) * (T : ℂ) + (T : ℂ) * mode v n by ring, Complex.exp_add]
    ring
  rw [hscale, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  have hs := average_spectrum_error hv hv' hT
  change ‖average T V - D‖ ≤ _ at hs
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hscore) hT))).trans hs

/-- An actual off-line zero forces large signed Gaussian averages at centers
in every sufficiently late interval of fixed length. -/
theorem signed_average_peaks {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1 / 4)
    (hsmall : v ≤ (ρ.re - 1 / 2) / (1 + ρ.im ^ 2)) :
    ∃ topScore L κ : ℝ, 1 / 2 + v / 8 < topScore ∧ 0 < L ∧ 0 < κ ∧
      ∀ᶠ a : ℝ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ T ∈ Icc a (a + L), ∃ hT : 0 ≤ T,
          κ * Real.exp (topScore * T) ≤
            sign * (average T ⟨v * T, mul_nonneg hv.le hT⟩).re := by
  obtain ⟨topScore, gap, hgap, hscore, hne, hfin, htail⟩ :=
    GaussianLeadingSpectrum.actual_leading_group (ρ := ⟨ρ, hz⟩) hβ hv hsmall
  let idx (n : ℕ) : GaussianLeadingSpectrum.StripZero :=
    ⟨actualData.zero n, actualData.zero_isNontrivial n⟩
  have hinj : Function.Injective idx := by
    intro i j h
    exact actualData.zero_injective (congrArg Subtype.val h)
  have hidx : Function.Surjective idx := by
    intro z
    obtain ⟨n, hn⟩ := actualData.zero_exhaustive z.property
    exact ⟨n, Subtype.ext hn⟩
  let s := (hfin.preimage hinj.injOn).toFinset
  have hs (n : ℕ) : n ∈ s ↔ (mode v n).re = topScore := by
    exact (hfin.preimage hinj.injOn).mem_toFinset
  have hsne : s.Nonempty := by
    obtain ⟨z, hz'⟩ := hne
    obtain ⟨n, rfl⟩ := hidx z
    exact ⟨n, (hs n).mpr hz'⟩
  have hst (n : ℕ) (hn : n ∉ s) : (mode v n).re ≤ topScore - gap :=
    (htail (idx n)).resolve_left fun h => hn ((hs n).mpr h)
  obtain ⟨L, κ, hL, hk, hex, hb⟩ := dominant_modes hv.le hgap s hs hst hsne
  have htop : 0 ≤ topScore := by linarith
  let err (T : ℝ) :=
    (6 + coefficientMass) * Real.exp (-T / 2) + coefficientMass * Real.exp (-gap * T)
  have herr : Tendsto err atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => Real.exp (-(1 / 2 : ℝ) * T)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num))
    have h2 : Tendsto (fun T : ℝ => Real.exp (-gap * T)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hgap))
    simpa only [err, mul_zero, zero_add,
      show ∀ T : ℝ, -(1 / 2 : ℝ) * T = -T / 2 by intro T; ring] using
      (h1.const_mul (6 + coefficientMass)).add (h2.const_mul coefficientMass)
  obtain ⟨A, hA⟩ := eventually_atTop.mp (herr.eventually_lt_const (half_pos hk))
  refine ⟨topScore, L, κ / 2, hscore, hL, half_pos hk, ?_⟩
  filter_upwards [eventually_ge_atTop (max A 0)] with a ha sign hsign
  have hA0 := (le_max_left _ _).trans ha
  have ha0 := (le_max_right _ _).trans ha
  obtain ⟨T, hT, hlead⟩ : ∃ T ∈ Icc a (a + L),
      κ < sign * (FiniteSpectralOscillation.series s distinctCoeff (frequency v) T).re := by
    rcases hsign with rfl | rfl
    · simpa only [one_mul] using (hex a).2
    · obtain ⟨t, ht, he⟩ := (hex a).1
      exact ⟨t, ht, by linarith⟩
  have hT0 := ha0.trans hT.1
  refine ⟨T, hT, hT0, ?_⟩
  let V : NNReal := ⟨v * T, mul_nonneg hv.le hT0⟩
  let F := (Real.exp (-topScore * T) : ℂ) * average T V
  let Q := FiniteSpectralOscillation.series s distinctCoeff (frequency v) T
  have hclose : ‖F - Q‖ < κ / 2 := by
    have ht := norm_sub_le F (normalized v topScore T)
    have hq := norm_add_le (F - normalized v topScore T) (normalized v topScore T - Q)
    rw [show F - normalized v topScore T + (normalized v topScore T - Q) = F - Q by abel] at hq
    have h₁ := normalized_average_error hv.le hv' hT0 htop
    have h₂ := hb T hT0
    exact (hq.trans (add_le_add h₁ h₂)).trans_lt (hA T (hA0.trans hT.1))
  have hR := (Complex.abs_re_le_norm (F - Q)).trans hclose.le
  rw [Complex.sub_re] at hR
  have hF : κ / 2 ≤ sign * F.re := by
    have lo := (abs_le.mp hR).1
    have hi := (abs_le.mp hR).2
    change κ < sign * Q.re at hlead
    rcases hsign with rfl | rfl <;> linarith
  dsimp only [F] at hF
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hF
  rw [show -topScore * T = -(topScore * T) by ring, Real.exp_neg] at hF
  rw [show sign * ((Real.exp (topScore * T))⁻¹ * (average T V).re) =
    (sign * (average T V).re) / Real.exp (topScore * T) by ring] at hF
  exact (le_div_iff₀ (Real.exp_pos _)).mp hF

/-- A lower bound on an actual log-scale window survives Gaussian averaging
up to the two exponentially small tails. -/
private theorem average_lower_of_window {T v d a b C sign : ℝ}
    (hT : 0 < T) (hd : 0 < d) (hd' : d ≤ 1) (hv : 0 < v) (hsmall : v ≤ d ^ 2 / 32)
    (ha : a ≤ (1 - d) * T) (hb : (1 + d) * T ≤ b) (hC : 0 ≤ C)
    (hSign : |sign| = 1)
    (hwindow : ∀ t ∈ Icc a b, -C * Real.exp (t / 2) ≤ sign * logHinge t) :
    -C * Real.exp ((1 / 2 + v / 8) * T) -
      2 * (coefficientMass + 6) * Real.exp (-2 * T) ≤
        sign * (average T ⟨v * T, (mul_pos hv hT).le⟩).re := by
  let V : NNReal := ⟨v * T, (mul_pos hv hT).le⟩
  let μ := gaussianReal T V
  let M := coefficientMass + 6
  let H := (Ioi (0 : ℝ)).indicator (fun t => sign * logHinge t)
  let E₁ := (Iio a).indicator Real.exp
  let E₂ := (Ioi b).indicator Real.exp
  let low := fun t : ℝ => -C * Real.exp (t / 2) - M * E₁ t - M * E₂ t
  have hM : 0 ≤ M := by
    have h : 0 ≤ coefficientMass := tsum_nonneg fun _ => norm_nonneg _
    dsimp [M]
    linarith
  have hExp : Integrable Real.exp μ := by
    simpa only [one_mul] using
      (integrable_exp_mul_gaussianReal (μ := T) (v := V) 1)
  have hhalf (t : ℝ) : t / 2 = (1 / 2 : ℝ) * t := by ring
  have hhalf_fun : (fun t : ℝ => Real.exp (t / 2)) =
      fun t : ℝ => Real.exp ((1 / 2 : ℝ) * t) :=
    funext fun t => congrArg Real.exp (hhalf t)
  have hHalf : Integrable (fun t : ℝ => Real.exp (t / 2)) μ := by
    rw [hhalf_fun]
    exact integrable_exp_mul_gaussianReal (μ := T) (v := V) (1 / 2)
  have hH : Integrable H μ := by
    apply (hExp.const_mul M).mono' ((continuous_const.mul logHinge_continuous).measurable.indicator
      measurableSet_Ioi).aestronglyMeasurable
    filter_upwards with t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem ht, Real.norm_eq_abs]
      change |sign * logHinge t| ≤ M * Real.exp t
      rw [abs_mul, hSign, one_mul]
      exact logHinge_growth ht
    · rw [indicator_of_notMem ht, norm_zero]
      exact mul_nonneg hM (Real.exp_nonneg _)
  have h₁ : Integrable E₁ μ :=
    (hExp.integrableOn : IntegrableOn Real.exp (Iio a) μ).integrable_indicator measurableSet_Iio
  have h₂ : Integrable E₂ μ :=
    (hExp.integrableOn : IntegrableOn Real.exp (Ioi b) μ).integrable_indicator measurableSet_Ioi
  have hlow : Integrable low μ := ((hHalf.const_mul (-C)).sub (h₁.const_mul M)).sub
    (h₂.const_mul M)
  have hpoint (t : ℝ) : low t ≤ H t := by
    have hn₁ : 0 ≤ E₁ t := by
      dsimp [E₁]
      exact indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
    have hn₂ : 0 ≤ E₂ t := by
      dsimp [E₂]
      exact indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
    have hn₀ := mul_nonneg hC (Real.exp_nonneg (t / 2))
    have hprod₁ := mul_nonneg hM hn₁
    have hprod₂ := mul_nonneg hM hn₂
    by_cases ht : 0 < t
    · rw [show H t = sign * logHinge t from indicator_of_mem ht _]
      have hg := (abs_le.mp (calc
        |sign * logHinge t| = |logHinge t| := by rw [abs_mul, hSign, one_mul]
        _ ≤ M * Real.exp t := logHinge_growth ht)).1
      by_cases hmem : t ∈ Icc a b
      · dsimp [low]
        linarith [hwindow t hmem]
      · have ht' : t < a ∨ b < t := by
          by_contra! hc
          exact hmem ⟨hc.1,hc.2⟩
        rcases ht' with hlt | hgt
        · have he : E₁ t = Real.exp t :=
            indicator_of_mem (show t ∈ Iio a from hlt) Real.exp
          dsimp [M] at *
          dsimp [low]
          rw [he]
          linarith only [hg, hn₀, hprod₂]
        · have he : E₂ t = Real.exp t :=
            indicator_of_mem (show t ∈ Ioi b from hgt) Real.exp
          dsimp [M] at *
          dsimp [low]
          rw [he]
          linarith only [hg, hn₀, hprod₁]
    · rw [show H t = 0 from indicator_of_notMem ht _]
      dsimp [low]
      linarith only [hn₀,hprod₁,hprod₂]
  have hEq : sign * (average T V).re = ∫ t, H t ∂μ := by
    unfold average
    rw [← integral_indicator measurableSet_Ioi]
    let H₀ := (Ioi (0 : ℝ)).indicator logHinge
    have he : (Ioi (0 : ℝ)).indicator (fun t => (logHinge t : ℂ)) = fun t => (H₀ t : ℂ) := by
      ext t
      by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [H₀,ht]
    rw [he, integral_complex_ofReal, Complex.ofReal_re]
    have hH₀ : H = fun t => sign * H₀ t := by
      funext t
      by_cases ht : t ∈ Ioi (0 : ℝ) <;> simp [H,H₀,ht]
    rw [hH₀, integral_const_mul]
  have htail := outside_window_exp_bound hT hd hd' hv hsmall ha hb
  change (∫ t in Iio a, Real.exp t ∂μ) ≤ _ ∧
    (∫ t in Ioi b, Real.exp t ∂μ) ≤ _ at htail
  have hHalfEq : (∫ t : ℝ, Real.exp (t / 2) ∂μ) = Real.exp ((1 / 2 + v / 8) * T) := by
    rw [hhalf_fun]
    change mgf (fun t : ℝ => t) (gaussianReal T V) (1 / 2) = _
    rw [mgf_fun_id_gaussianReal]
    change Real.exp (T * (1 / 2) + v * T * (1 / 2) ^ 2 / 2) = _
    apply congrArg Real.exp
    ring
  rw [hEq]
  refine le_trans ?_ (integral_mono hlow hH hpoint)
  have hlowEq : (∫ t, low t ∂μ) =
      (∫ t, -C * Real.exp (t / 2) ∂μ) - (∫ t, M * E₁ t ∂μ) -
        (∫ t, M * E₂ t ∂μ) :=
    (integral_sub (f := fun t => -C * Real.exp (t / 2) - M * E₁ t)
      (g := fun t => M * E₂ t) ((hHalf.const_mul (-C)).sub (h₁.const_mul M))
      (h₂.const_mul M)).trans
      (congrArg (fun z : ℝ => z - ∫ t, M * E₂ t ∂μ)
        (integral_sub (f := fun t => -C * Real.exp (t / 2))
          (g := fun t => M * E₁ t) (hHalf.const_mul (-C)) (h₁.const_mul M)))
  rw [hlowEq, integral_const_mul,
    integral_const_mul, integral_const_mul, hHalfEq,
    show (∫ t, E₁ t ∂μ) = ∫ t in Iio a, Real.exp t ∂μ from integral_indicator measurableSet_Iio,
    show (∫ t, E₂ t ∂μ) = ∫ t in Ioi b, Real.exp t ∂μ from integral_indicator measurableSet_Ioi]
  have he₁ := mul_le_mul_of_nonneg_left htail.1 hM
  have he₂ := mul_le_mul_of_nonneg_left htail.2 hM
  dsimp [M] at *
  linarith only [he₁, he₂]

/-- Each sufficiently late logarithmic interval of fixed relative width
contains both signs of the triangular ramp discrepancy beyond any square-root bound. -/
theorem signed_peaks_in_log_windows {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) {B C : ℝ} (hB : 1 < B) (hC : 0 ≤ C) :
    ∀ᶠ Y : ℝ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      ∃ t ∈ Icc Y (B * Y), C * Real.exp (t / 2) < sign * logHinge t := by
  let a := (1 + B) / 2
  let d := (B - 1) / (4 * B)
  have hB0 : 0 < B := zero_lt_one.trans hB
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  have haB : a ≤ B := by dsimp [a]; linarith
  have hd : 0 < d := div_pos (sub_pos.mpr hB) (by positivity)
  have hdB : d * B = (B - 1) / 4 := by dsimp [d]; field_simp
  have hd' : d ≤ 1 := by
    apply le_of_mul_le_mul_right _ hB0
    rw [hdB, one_mul]
    linarith
  let v := min (1 / 4 : ℝ) (min (d ^ 2 / 32) ((ρ.re - 1 / 2) / (1 + ρ.im ^ 2)))
  have hv : 0 < v := lt_min (by norm_num)
    (lt_min (by positivity) (div_pos (sub_pos.mpr hβ) (by positivity)))
  have hv₁ : v ≤ 1 / 4 := min_le_left _ _
  have hv₂ : v ≤ d ^ 2 / 32 := (min_le_right _ _).trans (min_le_left _ _)
  have hv₃ : v ≤ (ρ.re - 1 / 2) / (1 + ρ.im ^ 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨score, L, κ, hscoreAbove, hL, hκ, hpeaks⟩ := signed_average_peaks hz hβ hv hv₁ hv₃
  let q := 1 / 2 + v / 8
  let M := 2 * (coefficientMass + 6)
  have hq : q < score := hscoreAbove
  have hscorePositive : 0 < score := lt_trans (show 0 < q by dsimp [q]; positivity) hq
  have hdecay (c : ℝ) (hc : c < 0) :
      Tendsto (fun T : ℝ => Real.exp (c * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
  have hsmall : ∀ᶠ T : ℝ in atTop,
      C * Real.exp ((q - score) * T) + M * Real.exp ((-2 - score) * T) < κ := by
    have h₁ := (hdecay (q - score) (sub_neg.mpr hq)).const_mul C
    have h₂ := (hdecay (-2 - score) (by linarith)).const_mul M
    have h := h₁.add h₂
    rw [mul_zero, mul_zero, add_zero] at h
    exact h.eventually_lt_const hκ
  obtain ⟨A, hA⟩ := eventually_atTop.mp hpeaks
  obtain ⟨D, hD⟩ := eventually_atTop.mp hsmall
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop A,
    eventually_ge_atTop D, eventually_ge_atTop (8 * L / (B - 1))] with Y hY hYA hYD hYL
  intro sign hsign
  by_contra! hwindow
  have hYa : Y ≤ a * Y := le_mul_of_one_le_left (by linarith) ha1
  have hsignAbs : |-sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  obtain ⟨T, hT, _, hpeak⟩ := hA (a * Y) (hYA.trans hYa) sign hsign
  have hTY := hYa.trans hT.1
  have hT0 : 0 < T := lt_of_lt_of_le (by linarith) hTY
  have hda := mul_le_mul_of_nonneg_left haB hd.le
  rw [hdB] at hda
  have hleft : Y ≤ (1 - d) * T := by
    have hh : 1 ≤ (1 - d) * a := by dsimp [a] at hda ⊢; nlinarith
    calc
      Y ≤ ((1 - d) * a) * Y := le_mul_of_one_le_left (by linarith) hh
      _ = (1 - d) * (a * Y) := by ring
      _ ≤ (1 - d) * T := mul_le_mul_of_nonneg_left hT.1 (sub_nonneg.mpr hd')
  have hright : (1 + d) * T ≤ B * Y := by
    have hh : (1 + d) * a ≤ B - (B - 1) / 4 := by dsimp [a] at hda ⊢; nlinarith
    have hY' : 8 * L ≤ Y * (B - 1) := (div_le_iff₀ (sub_pos.mpr hB)).mp hYL
    have hL' : (1 + d) * L ≤ 2 * L := mul_le_mul_of_nonneg_right (by linarith) hL.le
    calc
      (1 + d) * T ≤ (1 + d) * (a * Y + L) := mul_le_mul_of_nonneg_left hT.2 (by positivity)
      _ = ((1 + d) * a) * Y + (1 + d) * L := by ring
      _ ≤ (B - (B - 1) / 4) * Y + 2 * L :=
        add_le_add (mul_le_mul_of_nonneg_right hh (by linarith)) hL'
      _ ≤ B * Y := by nlinarith
  have hlo := average_lower_of_window hT0 hd hd' hv hv₂ hleft hright hC hsignAbs
    (fun t ht => by linarith [hwindow t ht])
  have hupper : κ * Real.exp (score * T) ≤ C * Real.exp (q * T) + M * Real.exp (-2 * T) := by
    change -C * Real.exp (q * T) - M * Real.exp (-2 * T) ≤
      -sign * (average T ⟨v * T, (mul_pos hv hT0).le⟩).re at hlo
    linarith only [hlo, hpeak]
  have hcontr := mul_lt_mul_of_pos_right (hD T (hYD.trans hTY)) (Real.exp_pos (score * T))
  rw [add_mul, mul_assoc C, mul_assoc M, ← Real.exp_add, ← Real.exp_add,
    show (q - score) * T + score * T = q * T by ring,
    show (-2 - score) * T + score * T = -2 * T by ring] at hcontr
  exact (not_lt_of_ge hupper) hcontr

/-- Every sufficiently late power window contains positive and negative
triangular ramp discrepancies beyond any fixed square-root bound. -/
theorem signed_peaks_in_power_windows {ρ : ℂ} (hz : Zeta23.IsNontrivialZero ρ)
    (hβ : 1 / 2 < ρ.re) {B C : ℝ} (hB : 1 < B) (hC : 0 ≤ C) :
    ∀ᶠ X : ℝ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      ∃ x ∈ Icc X (X ^ B), C * Real.sqrt x <
        sign * (U (4 * x) - 3 * U (2 * x) + 2 * U x) := by
  have h := Real.tendsto_log_atTop.eventually (signed_peaks_in_log_windows hz hβ hB hC)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX hX1 sign hsign
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  obtain ⟨t, ht, hs⟩ := hX sign hsign
  refine ⟨Real.exp t, ⟨?_, ?_⟩, ?_⟩
  · exact Real.exp_log hX0 ▸ Real.exp_le_exp.mpr ht.1
  · rw [Real.rpow_def_of_pos hX0]
    exact Real.exp_le_exp.mpr (by linarith only [ht.2])
  · rw [logHinge_eq] at hs
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp,
      show t * (1 / 2 : ℝ) = t / 2 by ring]
    exact hs

end GaussianActualWindowAssembly

#print axioms GaussianActualWindowAssembly.average_spectrum_error
#print axioms GaussianActualWindowAssembly.signed_average_peaks
#print axioms GaussianActualWindowAssembly.signed_peaks_in_log_windows
#print axioms GaussianActualWindowAssembly.signed_peaks_in_power_windows
