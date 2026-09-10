/- GID: D5/S3/Weil/ZetaBridge/FermiMellin
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FermiMellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.MellinTransform]
   utility: none
   digest: The actual Fermi Mellin integral, its removable value, and the Salem RH criterion. -/
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic
import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction

/-!
Copyright 2026 David Sanftenberg. Licensed under Apache-2.0.
Modified for trureturing: reduced private proof slice, finite sums inlined,
target-pin adaptation. Full license and source map:
Library/Weil/sanftenberg2026fermi.md.
No upstream eta object or analytic continuation is transplanted.
-/
open Complex Filter MeasureTheory Set
open scoped Classical Topology
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Weil.ZetaBridge.FermiMellin
noncomputable section

private def fermi (t : ℝ) : ℝ := (1 + Real.exp t)⁻¹

private def fermiOne (t : ℝ) : ℝ := fermi t * (fermi t - 1)

private theorem fermi_bounds (t : ℝ) : 0 < fermi t ∧ fermi t < 1 := by
  have he := Real.exp_pos t
  constructor
  · exact inv_pos.mpr (by linarith)
  · exact inv_lt_one_of_one_lt₀ (by linarith)

private theorem fermi_le_exp_neg (t : ℝ) : fermi t ≤ Real.exp (-t) := by
  rw [fermi, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos t)
    (by linarith : Real.exp t ≤ 1 + Real.exp t)

private theorem hasDerivAt_fermi (t : ℝ) : HasDerivAt fermi (fermiOne t) t := by
  have hne : 1 + Real.exp t ≠ 0 := by positivity
  convert! ((Real.hasDerivAt_exp t).const_add 1).inv hne using 1
  dsimp only [fermiOne, fermi]
  field_simp
  ring

private theorem continuous_fermi : Continuous fermi :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_fermi t).continuousAt

private def mellinExponential (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)

private theorem integrableOn_mellinExponential {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (mellinExponential s n) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hs).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.mul
    · apply continuousOn_of_forall_continuousAt
      intro t ht
      have hc : ContinuousAt (fun z : ℂ ↦ z ^ (s - 1)) (t : ℂ) :=
        continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)
      exact hc.comp continuous_ofReal.continuousAt
    · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [mellinExponential, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
    simp only [Complex.sub_re, Complex.one_re]
    rw [mul_comm (Real.exp (-t))]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_of_lt ht) _)
    apply Real.exp_le_exp.mpr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have ht0 : 0 < t := ht
    nlinarith

private theorem integral_mellinExponential {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in Ioi (0 : ℝ), mellinExponential s n t) = Complex.Gamma s * (n : ℂ) ^ (-s) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hnR
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← neg_mul] at hi
  change (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)) = _
  rw [hi, one_div, Complex.inv_cpow_ofReal_nonneg hnR.le, ← Complex.cpow_neg]
  simp only [Complex.ofReal_natCast]
  exact mul_comm _ _

private def fermiPartial (N : ℕ) (t : ℝ) : ℝ := fermi t * (1 - (Real.exp (-t) ^ 2) ^ N)

private theorem fermi_pair_factor (t : ℝ) :
    fermi t * (1 - Real.exp (-t) ^ 2) = Real.exp (-t) - Real.exp (-t) ^ 2 := by
  rw [fermi, Real.exp_neg]
  field_simp
  ring

private theorem sum_exponential_pairs_eq_fermiPartial (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range N, (Real.exp (-t) ^ (2 * n + 1) - Real.exp (-t) ^ (2 * n + 2))) =
      fermiPartial N t := by
  induction N with
  | zero => simp [fermiPartial]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [fermiPartial, pow_add, pow_mul, pow_one]
    have h := fermi_pair_factor t
    linear_combination -((Real.exp (-t) ^ 2) ^ N) * h

private theorem fermiPartial_bounds (N : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ fermiPartial N t ∧ fermiPartial N t ≤ fermi t := by
  have hE : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hEle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp : 0 ≤ (Real.exp (-t) ^ 2) ^ N := by positivity
  have hp1 : (Real.exp (-t) ^ 2) ^ N ≤ 1 := pow_le_one₀ (by positivity) (pow_le_one₀ hE hEle)
  have hf := (fermi_bounds t).1.le
  unfold fermiPartial
  exact ⟨mul_nonneg hf (sub_nonneg.mpr hp1), by nlinarith⟩

private theorem fermiPartial_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ ↦ fermiPartial N t) atTop (𝓝 (fermi t)) := by
  have hp : Real.exp (-t) ^ 2 < 1 := by
    have hE := Real.exp_pos (-t)
    have hE1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    nlinarith
  simpa only [fermiPartial, sub_zero, mul_one] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp)).const_mul (fermi t)

private theorem integral_mellin_fermiPartial {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (fermiPartial N t : ℂ)) =
      Complex.Gamma s * (∑ n ∈ Finset.range N, (((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s))) := by
  have he (t : ℝ) : (t : ℂ) ^ (s - 1) * (fermiPartial N t : ℂ) =
      ∑ n ∈ Finset.range N, (mellinExponential s (2 * n + 1) t - mellinExponential s (2 * n + 2) t) := by
    rw [← sum_exponential_pairs_eq_fermiPartial, Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    simp only [Complex.ofReal_sub, mul_sub, mellinExponential, ← Real.exp_nat_mul, mul_neg, neg_mul]
  simp_rw [he]
  rw [integral_finsetSum (Finset.range N)
    (f := fun n t ↦ mellinExponential s (2 * n + 1) t - mellinExponential s (2 * n + 2) t)
    (fun n _ ↦ (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 1)).sub
    (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 2)))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [integral_sub (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 1))
    (integrableOn_mellinExponential hs (by omega : 1 ≤ 2 * n + 2)),
    integral_mellinExponential hs (by omega : 1 ≤ 2 * n + 1),
    integral_mellinExponential hs (by omega : 1 ≤ 2 * n + 2)]
  ring

private def mellinFermi (s : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) * (fermi t : ℂ)

private theorem continuousOn_mellin_mul (s : ℂ) {f : ℝ → ℝ} (hf : Continuous f) :
    ContinuousOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * (f t : ℂ)) (Ioi 0) := by
  apply ContinuousOn.mul
  · apply continuousOn_of_forall_continuousAt
    intro t ht
    have hc : ContinuousAt (fun z : ℂ ↦ z ^ (s - 1)) (t : ℂ) :=
      continuousAt_cpow_const (ofReal_mem_slitPlane.mpr ht)
    exact hc.comp continuous_ofReal.continuousAt
  · exact (continuous_ofReal.comp hf).continuousOn

private theorem integrableOn_mellinFermi {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (mellinFermi s) (Ioi 0) := by
  apply (Real.GammaIntegral_convergent hs).mono'
    ((continuousOn_mellin_mul s continuous_fermi).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (fermi_bounds t).1, norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
  simp only [Complex.sub_re, Complex.one_re]
  exact (mul_le_mul_of_nonneg_left (fermi_le_exp_neg t) (Real.rpow_nonneg (le_of_lt ht) _)).trans_eq (mul_comm _ _)

private theorem integral_mellin_fermiPartial_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (fermiPartial N t : ℂ))
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), mellinFermi s t)) := by
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ ↦ Real.exp (-t) * t ^ (s.re - 1))
  · intro N
    apply (continuousOn_mellin_mul s _).aestronglyMeasurable measurableSet_Ioi
    exact continuous_fermi.mul
      (continuous_const.sub (((continuous_neg.rexp).pow 2).pow N))
  · exact Real.GammaIntegral_convergent hs
  · intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fermiPartial_bounds N ht).1, norm_cpow_eq_rpow_re_of_pos ht (s - 1)]
    simp only [Complex.sub_re, Complex.one_re]
    exact (mul_le_mul_of_nonneg_left ((fermiPartial_bounds N ht).2.trans (fermi_le_exp_neg t))
      (Real.rpow_nonneg (le_of_lt ht) _)).trans_eq (mul_comm _ _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ((continuous_ofReal.continuousAt.tendsto).comp (fermiPartial_tendsto ht)).const_mul _

private lemma pairedEtaFactor_eq_zero_implies_re_eq_one
    {s : ℂ} (hfactor : 1 - (2 : ℂ) * (2 : ℂ) ^ (-s) = 0) :
    s.re = 1 := by
  have heq : (2 : ℂ) * (2 : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hfactor).symm
  have hcpow : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    change ‖((2 : ℝ) : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  have hrpow : (2 : ℝ) ^ (1 - s.re) = (2 : ℝ) ^ (0 : ℝ) := by
    calc
      (2 : ℝ) ^ (1 - s.re) =
          (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s.re) := by
        rw [show 1 - s.re = (1 : ℝ) + (-s.re) by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = 2 * ‖(2 : ℂ) ^ (-s)‖ := by
        rw [Real.rpow_one, hcpow]
      _ = ‖(2 : ℂ) * (2 : ℂ) ^ (-s)‖ := by
        rw [norm_mul]
        norm_num
      _ = 1 := by rw [heq]; norm_num
      _ = (2 : ℝ) ^ (0 : ℝ) := by norm_num
  have hexponent : 1 - s.re = 0 :=
    (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      hrpow
  linarith

private lemma pairedEtaFactor_ne_zero_of_re_lt_one
    {s : ℂ} (hs : s.re < 1) :
    1 - (2 : ℂ) * (2 : ℂ) ^ (-s) ≠ 0 := by
  intro hfactor
  linarith [pairedEtaFactor_eq_zero_implies_re_eq_one hfactor]


private lemma paired_sum_eq (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (((2 * n + 1 : ℕ) : ℂ) ^ (-s) -
      ((2 * n + 2 : ℕ) : ℂ) ^ (-s))) =
    ∑ n ∈ Finset.range (2 * N), (-1 : ℂ) ^ n * (n + 1 : ℂ) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
    push_cast
    ring

theorem fermi_mellin_integrable (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) /
      ((Real.exp (x * t) : ℂ) + 1)) (Ioi 0) := by
  have h : MellinConvergent (fun t => (fermi t : ℂ)) s :=
    integrableOn_mellinFermi hs
  simpa only [MellinConvergent, smul_eq_mul, fermi, ofReal_inv, ofReal_add,
    ofReal_one, add_comm (1 : ℂ), div_eq_mul_inv] using
    (MellinConvergent.comp_mul_left hx).mpr h

theorem fermi_mellin_eq_of_ne_one (x : ℝ) (hx : 0 < x) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) / ((Real.exp (x * t) : ℂ) + 1)) =
      (x : ℂ) ^ (-s) * Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s := by
  have hnat := AlternatingZetaContinuation.tendsto_alternating_partialSums_eta_of_ne_one s hs hs1
  have hco : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun N => by change N ≤ 2 * N; omega) tendsto_id
  have hlim := (hnat.comp hco).const_mul (Complex.Gamma s)
  dsimp only [Function.comp_def] at hlim
  simp_rw [← paired_sum_eq s, ← integral_mellin_fermiPartial hs] at hlim
  have hi := tendsto_nhds_unique (integral_mellin_fermiPartial_tendsto hs) hlim
  have hscale := mellin_comp_mul_left (fun t => (fermi t : ℂ)) s hx
  change _ = (x : ℂ) ^ (-s) * (∫ t in Ioi (0 : ℝ), mellinFermi s t) at hscale
  rw [hi] at hscale
  simpa only [mellin, smul_eq_mul, fermi, ofReal_inv, ofReal_add, ofReal_one,
    add_comm (1 : ℂ), div_eq_mul_inv, mul_assoc] using hscale

theorem fermi_mellin_product_tendsto_one (x : ℝ) (hx : 0 < x) :
    Tendsto (fun s : ℂ => (x : ℂ) ^ (-s) * Complex.Gamma s *
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) (𝓝[≠] (1 : ℂ))
      (𝓝 ((Real.log 2 : ℂ) / (x : ℂ))) := by
  have hd : HasDerivAt (fun s : ℂ => 1 - (2 : ℂ) ^ (1 - s)) (Real.log 2 : ℂ) 1 := by
    convert! (((hasDerivAt_id (1 : ℂ)).const_sub 1).const_cpow
      (c := (2 : ℂ)) (Or.inl (by norm_num))).const_sub 1 using 1 <;> simp
  have hquot : Tendsto (fun s : ℂ => (1 - (2 : ℂ) ^ (1 - s)) / (s - 1))
      (𝓝[≠] 1) (𝓝 (Real.log 2 : ℂ)) := by
    simpa [slope_fun_def_field] using hd.tendsto_slope
  have hxcont : ContinuousAt (fun s : ℂ => (x : ℂ) ^ (-s)) 1 :=
    (differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))).continuousAt
  have ht := (hxcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))).mul
    (Complex.continuousAt_Gamma_one.tendsto.mono_left nhdsWithin_le_nhds)
  have hl := ht.mul (hquot.mul riemannZeta_residue_one)
  have he : (fun s : ℂ => (x : ℂ) ^ (-s) * Gamma s *
      ((1 - (2 : ℂ) ^ (1 - s)) / (s - 1) * ((s - 1) * riemannZeta s)))
      =ᶠ[𝓝[≠] 1] (fun s : ℂ => (x : ℂ) ^ (-s) * Gamma s *
      (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    field_simp
  simpa [Gamma_one, Complex.cpow_neg, div_eq_mul_inv, mul_comm] using hl.congr' he

private lemma continuousAt_mellin_fermi_one :
    ContinuousAt (mellin (fun t => (fermi t : ℂ))) 1 := by
  apply (mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := 0)
    (by norm_num) ((continuous_ofReal.comp continuous_fermi).continuousOn.locallyIntegrableOn
      measurableSet_Ioi) ?_ ?_ (by norm_num)).continuousAt
  · apply Asymptotics.isBigO_of_le
    intro t
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fermi_bounds t).1,
      abs_of_pos (Real.exp_pos _)] using fermi_le_exp_neg t
  · apply Asymptotics.isBigO_of_le
    intro t
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (fermi_bounds t).1] using
      (fermi_bounds t).2.le

theorem fermi_mellin_at_one (x : ℝ) (hx : 0 < x) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((1 : ℂ) - 1) /
      ((Real.exp (x * t) : ℂ) + 1)) = (Real.log 2 : ℂ) / (x : ℂ) := by
  have hc : ContinuousAt (fun s : ℂ => (x : ℂ) ^ (-s) *
      mellin (fun t => (fermi t : ℂ)) s) 1 :=
    ((differentiableAt_id.neg.const_cpow
      (Or.inl (ofReal_ne_zero.mpr hx.ne'))).continuousAt).mul continuousAt_mellin_fermi_one
  have hi : ContinuousAt (fun s : ℂ => ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) / ((Real.exp (x * t) : ℂ) + 1)) 1 := by
    have he (s : ℂ) : (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) / ((Real.exp (x * t) : ℂ) + 1)) =
        (x : ℂ) ^ (-s) * mellin (fun t => (fermi t : ℂ)) s := by
      simpa only [mellin, smul_eq_mul, fermi, ofReal_inv, ofReal_add, ofReal_one,
        add_comm (1 : ℂ), ← div_eq_mul_inv] using
        mellin_comp_mul_left (fun t => (fermi t : ℂ)) s hx
    simpa only [← he] using hc
  have hpos : ∀ᶠ s : ℂ in 𝓝[≠] 1, 0 < s.re :=
    nhdsWithin_le_nhds (continuous_re.continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < (1 : ℂ).re)))
  have hlim := (fermi_mellin_product_tendsto_one x hx).congr'
    (show _ =ᶠ[𝓝[≠] (1 : ℂ)] _ from by
      filter_upwards [hpos, self_mem_nhdsWithin] with s hs hs1
      exact (fermi_mellin_eq_of_ne_one x hx s hs hs1).symm)
  exact tendsto_nhds_unique (hi.tendsto.mono_left nhdsWithin_le_nhds) hlim

theorem fermi_mellin_identity (x : ℝ) (hx : 0 < x) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) /
      ((Real.exp (x * t) : ℂ) + 1)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) / ((Real.exp (x * t) : ℂ) + 1)) =
      (if s = 1 then (Real.log 2 : ℂ) / (x : ℂ) else
        (x : ℂ) ^ (-s) * Complex.Gamma s * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s) := by
  refine ⟨fermi_mellin_integrable x hx s hs, ?_⟩
  split_ifs with h
  · subst s
    exact fermi_mellin_at_one x hx
  · exact fermi_mellin_eq_of_ne_one x hx s hs h

theorem fermi_mellin_nonzero_iff_zeta_nonzero (s : ℂ)
    (hlo : (1 : ℝ) / 2 < s.re) (hhi : s.re < 1) :
    ((∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) / ((Real.exp t : ℂ) + 1)) ≠ 0 ↔
      riemannZeta s ≠ 0) := by
  have hs : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; simpa [h] using hhi
  have hf : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
    rw [show 1 - s = 1 + -s by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), cpow_one]
    exact pairedEtaFactor_ne_zero_of_re_lt_one hhi
  have hi := (fermi_mellin_identity 1 (by norm_num) s hs).2
  simp only [hs1, if_false, ofReal_one, one_cpow, one_mul] at hi
  rw [hi, mul_ne_zero_iff]
  simp [mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hs) hf]

theorem salem_mellin_nonvanishing_iff_rh :
    (∀ δ : ℝ, (1 : ℝ) / 2 < δ → δ < 1 → ∀ γ : ℝ,
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((δ : ℂ) - 1 + Complex.I * (γ : ℂ)) /
        ((Real.exp t : ℂ) + 1)) ≠ 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply RightHalfStripRiemannReduction.golden_right_half_strip_implies_rh
    intro s hz hlo hhi
    apply ((fermi_mellin_nonzero_iff_zeta_nonzero s hlo hhi).mp ?_) hz
    have he : (s.re : ℂ) - 1 + I * (s.im : ℂ) = s - 1 := by
      linear_combination Complex.re_add_im s
    simpa only [he] using h s.re hlo hhi s.im
  · intro h δ hlo hhi γ
    let s : ℂ := (δ : ℂ) + I * (γ : ℂ)
    have hs : s.re = δ := by simp [s]
    have hn : riemannZeta s ≠ 0 := by
      intro hz
      have htr : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
        rintro ⟨n, he⟩
        have hr := congrArg Complex.re he
        norm_num [hs] at hr
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hs1 : s ≠ 1 := by intro he; have := congrArg Complex.re he; simp [hs] at this; linarith
      have := h s hz htr hs1
      rw [hs] at this
      linarith
    have hi := (fermi_mellin_nonzero_iff_zeta_nonzero s (by rwa [hs]) (by rwa [hs])).mpr hn
    have he : (δ : ℂ) - 1 + I * (γ : ℂ) = s - 1 := by dsimp [s]; ring
    simpa only [he] using hi

#print axioms fermi_mellin_identity
#print axioms fermi_mellin_nonzero_iff_zeta_nonzero
#print axioms salem_mellin_nonvanishing_iff_rh
#print axioms fermi_mellin_product_tendsto_one
#print axioms fermi_mellin_at_one
#print axioms fermi_mellin_integrable
#print axioms fermi_mellin_eq_of_ne_one
end
end D5.S3.Weil.ZetaBridge.FermiMellin
