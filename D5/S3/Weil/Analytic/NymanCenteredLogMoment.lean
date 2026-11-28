/- GID: D5/S3/Weil/Analytic/NymanCenteredLogMoment
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanCenteredLogMoment
   mirror-E: none(waiver:logarithmic-moment-analysis)
   anchors: []
   utility: none
   digest: The first logarithmic moment of the centered prime sum is positive. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Analytic.NymanCenteredDirichletAtOne
import D5.S3.Weil.Analytic.NymanCenteredMoment
import D5.S3.Weil.Analytic.NymanWeightedMomentEndpoint

/-! The first logarithmic moment of the centered prime dilation sum. -/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

open private continuous_centeredPrimeDilations from D5.S3.Weil.Analytic.NymanCenteredBoundary
open private tendsto_zeta_normalized centeredPrimeConvolution_lSeries_eq_div from
  D5.S3.Weil.Analytic.NymanCenteredPrimeDirichlet
open private centered_mellin_factorization from D5.S3.Weil.Analytic.NymanCenteredMoment

namespace NymanCenteredLogMoment

open NymanPrimeDilations NymanCenteredMomentTail NymanCenteredBoundary NymanCenteredMoment
open NymanCenteredPrimeDirichlet NymanCenteredDirichletAtOne NymanWeightedMomentEndpoint
open NymanFixedRationalKernel (A b b_zero_off continuous_b mellin_formula)

theorem integrable_centeredPrime_log_weighted :
    IntegrableOn (fun x : ℝ => centeredPrimeDilations x * Real.log x / x ^ 2) (Ioi 1) := by
  obtain ⟨K, hK, hbound⟩ := centeredPrime_log_cube_bound
  obtain ⟨S, hS⟩ := eventually_atTop.mp hbound
  let T := max S 2
  have hT : 1 < T := (by norm_num : (1 : ℝ) < 2).trans_le (le_max_right _ _)
  have hcont : ContinuousOn (fun x : ℝ => centeredPrimeDilations x * Real.log x / x ^ 2)
      (Ici 1) := by
    refine (continuous_centeredPrimeDilations.continuousOn.mul ?_).div
      (continuous_id.pow 2).continuousOn ?_
    · exact fun x hx => (Real.continuousAt_log
        ((zero_lt_one.trans_le (mem_Ici.mp hx)).ne')).continuousWithinAt
    · exact fun x hx => pow_ne_zero 2 ((zero_lt_one.trans_le (mem_Ici.mp hx)).ne')
  have hcompact : IntegrableOn (fun x : ℝ => centeredPrimeDilations x * Real.log x / x ^ 2)
      (Icc 1 T) := (hcont.mono (fun _ hx => hx.1)).integrableOn_Icc
  have hDom : IntegrableOn (fun x : ℝ => K * (x⁻¹ / Real.log x ^ 2)) (Ioi T) :=
    (integrableOn_inv_div_log_sq_Ioi hT).const_mul K
  have htail : IntegrableOn (fun x : ℝ => centeredPrimeDilations x * Real.log x / x ^ 2)
      (Ioi T) := by
    have hcontTail := hcont.mono
      (show Ioi T ⊆ Ici (1 : ℝ) from fun _ hx => hT.le.trans (mem_Ioi.mp hx).le)
    apply hDom.mono' (hcontTail.aestronglyMeasurable measurableSet_Ioi)
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Eventually.of_forall
    intro x hx
    have hx₁ : 1 < x := hT.trans (mem_Ioi.mp hx)
    have hx₀ : 0 < x := zero_lt_one.trans hx₁
    have hlog : 0 < Real.log x := Real.log_pos hx₁
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hlog, abs_of_pos (pow_pos hx₀ 2)]
    calc
      _ ≤ (K * x / Real.log x ^ 3 * Real.log x) / x ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hS x ((le_max_left _ _).trans (mem_Ioi.mp hx).le))
            hlog.le) (pow_nonneg hx₀.le 2)
      _ = _ := by field_simp [hx₀.ne', hlog.ne']
  exact (hcompact.union htail).mono_set (fun x hx => by
    by_cases h : x ≤ T
    · exact Or.inl ⟨(mem_Ioi.mp hx).le, h⟩
    · exact Or.inr (lt_of_not_ge h))

private theorem mellin_centered_eq_weighted (t : ℝ) :
    mellin (fun x => (centeredPrimeDilations x : ℂ)) (-((1 + t : ℝ) : ℂ)) =
      Complex.ofReal (∫ x in Ioi (1 : ℝ), x ^ (-t) * (centeredPrimeDilations x / x ^ 2)) := by
  unfold mellin
  rw [← integral_complex_ofReal]
  have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ hx => zero_lt_one.trans (mem_Ioi.mp hx)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
    (fun x hx => by
      dsimp only
      rw [centeredPrimeDilations_eq_zero_of_le_one (le_of_not_gt hx.2), Complex.ofReal_zero,
        smul_zero])]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx₀ : 0 < x := zero_lt_one.trans (mem_Ioi.mp hx)
  have hcast : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx₀.ne'
  have hexp : -((1 + t : ℝ) : ℂ) - 1 = -(t : ℂ) + -(2 : ℂ) := by push_cast; ring
  dsimp only
  rw [hexp, Complex.cpow_add _ _ hcast, Complex.cpow_neg (x : ℂ) 2, Complex.cpow_two,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_cpow hx₀.le, Complex.ofReal_neg, div_eq_mul_inv]
  ring

/-- The ordinary Mellin moment of the fixed rational kernel. -/
def kernelMoment : ℝ :=
  ((A - 1) * (A ^ 2 - 1) * (A ^ 3 - 1) * (A ^ 4 - 1)) / 24

private theorem mellin_kernel_one :
    mellin (fun x => (b x : ℂ)) ((1 : ℝ) : ℂ) = (kernelMoment : ℂ) := by
  rw [Complex.ofReal_one, mellin_formula (by norm_num : 0 < (1 : ℂ).re)]
  have h₂ : (1 : ℂ) + 1 = 2 := by norm_num
  have h₃ : (1 : ℂ) + 2 = 3 := by norm_num
  have h₄ : (1 : ℂ) + 3 = 4 := by norm_num
  rw [h₂, h₃, h₄, Complex.cpow_one, Complex.cpow_two,
    Complex.cpow_ofNat _ 3, Complex.cpow_ofNat _ 4]
  norm_num [kernelMoment, A]

private theorem kernelMoment_pos : 0 < kernelMoment := by
  norm_num [kernelMoment, NymanFixedRationalKernel.A]

private theorem tendsto_add_one_right :
    Tendsto (fun t : ℝ => 1 + t) (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : Continuous (fun t : ℝ => 1 + t) := by fun_prop
    simpa only [add_zero] using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_add_of_pos_right _ (mem_Ioi.mp ht)

private theorem tendsto_centered_mellin_quotient :
    Tendsto (fun t : ℝ =>
      mellin (fun x => (centeredPrimeDilations x : ℂ)) (-((1 + t : ℝ) : ℂ)) / (t : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((centeredPrimeDirichletAtOne : ℂ) * (kernelMoment : ℂ))) := by
  have hkernel :
      Tendsto (fun σ : ℝ => mellin (fun x => (b x : ℂ)) (σ : ℂ))
        (𝓝[>] (1 : ℝ)) (𝓝 (kernelMoment : ℂ)) := by
    rw [← mellin_kernel_one]
    have hc := NymanDilationTransform.continuous_mellin_kernel
      (Complex.continuous_ofReal.comp continuous_b) (fun x hx => by simp [b_zero_off x hx])
    exact ((hc.comp Complex.continuous_ofReal).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hDiv := tendsto_centeredPrimeCoefficient_lSeries_at_one.div tendsto_zeta_normalized
    (one_ne_zero : (1 : ℂ) ≠ 0)
  rw [div_one] at hDiv
  have hlim := (hDiv.mul hkernel).comp tendsto_add_one_right
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  let σ : ℝ := 1 + t
  have ht₀ : 0 < t := mem_Ioi.mp ht
  have hs : 1 < (σ : ℂ).re := by
    simpa [σ] using lt_add_of_pos_right (1 : ℝ) ht₀
  have htz : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₀.ne'
  have hσt : (σ : ℂ) - 1 = (t : ℂ) := by dsimp [σ]; push_cast; ring
  change LSeries centeredPrimeCoefficientComplex (σ : ℂ) /
      (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) * mellin (fun x => (b x : ℂ)) (σ : ℂ) =
    mellin (fun x => (centeredPrimeDilations x : ℂ)) (-(σ : ℂ)) / (t : ℂ)
  rw [centered_mellin_factorization hs, centeredPrimeConvolution_lSeries_eq_div hs, hσt]
  field_simp [htz, riemannZeta_ne_zero_of_one_lt_re hs]

/-- The first logarithmic moment is fixed by the finite part of the centered prime series. -/
theorem integral_centeredPrime_log_weighted :
    (∫ x in Ioi (1 : ℝ), centeredPrimeDilations x * Real.log x / x ^ 2) =
      -centeredPrimeDirichletAtOne * kernelMoment := by
  have hC := integrable_centeredPrime_weighted.mono_set
    (show Ioi (1 : ℝ) ⊆ Ioi 0 from fun _ hx => zero_lt_one.trans (mem_Ioi.mp hx))
  have hreal := tendsto_weighted_moment_difference_quotient hC
    integrable_centeredPrime_log_weighted
  simp only [integral_centeredPrime_weighted_eq_zero, zero_sub] at hreal
  have hcomplex := hreal.ofReal
  have hlim : Tendsto (fun t : ℝ =>
      -(mellin (fun x => (centeredPrimeDilations x : ℂ)) (-((1 + t : ℝ) : ℂ)) / (t : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.ofReal (∫ x in Ioi (1 : ℝ), centeredPrimeDilations x * Real.log x / x ^ 2))) := by
    apply hcomplex.congr'
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [mellin_centered_eq_weighted, Complex.ofReal_div, Complex.ofReal_neg, neg_div]
  have h := tendsto_nhds_unique hlim tendsto_centered_mellin_quotient.neg
  exact Complex.ofReal_injective (by simpa [Complex.ofReal_mul, Complex.ofReal_neg] using h)

theorem integral_centeredPrime_log_weighted_pos :
    0 < ∫ x in Ioi (1 : ℝ), centeredPrimeDilations x * Real.log x / x ^ 2 := by
  rw [integral_centeredPrime_log_weighted]
  exact mul_pos (neg_pos.mpr centeredPrimeDirichletAtOne_neg) kernelMoment_pos

end NymanCenteredLogMoment
