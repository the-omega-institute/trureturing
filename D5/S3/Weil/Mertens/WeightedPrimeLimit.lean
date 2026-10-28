/- GID: D5/S3/Weil/Mertens/WeightedPrimeLimit
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/WeightedPrimeLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute Chebyshev error tails and original weighted prime limits. -/

import D5.S3.Weil.PrimeNumberTheorem.MediumPNT
import D5.S3.Weil.Mertens.Estimates
import D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Quantitative PNT controls the actual Chebyshev tail and original weighted sums. -/

namespace D5.S3.Weil.Mertens.WeightedPrimeLimit

open Real Set MeasureTheory Filter Asymptotics
open scoped BigOperators Topology

noncomputable section

/-- Absolute Lebesgue integrability of the actual Chebyshev error kernel. -/
theorem chebyshev_error_kernel_integrable :
    IntegrableOn (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) (Ioi 1) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨D, hD, hbound⟩ := isBigO_iff'.mp hO
  obtain ⟨A, hA⟩ := eventually_atTop.mp hbound
  let B : ℝ := max A 2
  have hB : (2 : ℝ) ≤ B := le_max_right _ _
  have hmeas : Measurable (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) :=
    (Chebyshev.psi_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)
  have hexp : IntegrableOn
      (fun v : ℝ => Real.exp (-c * v ^ ((1 : ℝ) / 10))) (Ioi 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (0 : ℝ)) (p := (1 : ℝ) / 10) (b := c)
        (by norm_num) (by norm_num) hc)
  have hlog : IntegrableOn
      (fun u : ℝ => Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) / u)
      (Ioi 1) := by
    simpa only [Real.log_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (integrableOn_comp_log_Ioi
        (fun v : ℝ => Real.exp (-c * v ^ ((1 : ℝ) / 10))) one_pos).mpr
        (by simpa only [Real.log_one] using hexp)
  have htail : IntegrableOn
      (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) (Ioi B) := by
    refine ((hlog.mono_set (Ioi_subset_Ioi (by linarith : (1 : ℝ) ≤ B))).const_mul D).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := by
      have huB : B < u := hu
      linarith
    have hub : A ≤ u := (le_max_left A 2).trans hu.le
    have hp : |Chebyshev.psi u - u| ≤
        D * (u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10))) := by
      simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul,
        abs_of_pos hu0, abs_of_pos (Real.exp_pos _)] using hA u hub
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg u)]
    calc
      _ ≤ (D * (u * Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) )) / u ^ 2 :=
        div_le_div_of_nonneg_right hp (sq_nonneg u)
      _ = D * (Real.exp (-c * (Real.log u) ^ ((1 : ℝ) / 10)) / u) := by
        field_simp [hu0.ne']
        <;> ring
  have hlocal : IntegrableOn
      (fun u : ℝ => (Chebyshev.psi u - u) / u ^ 2) (Ioc 1 B) := by
    refine IntegrableOn.of_bound (by simp) hmeas.aestronglyMeasurable
      (Chebyshev.psi B + B) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg u)]
    calc
      _ ≤ |Chebyshev.psi u - u| :=
        div_le_self (abs_nonneg _) (by nlinarith [hu.1])
      _ ≤ |Chebyshev.psi u| + |u| := abs_sub _ _
      _ = Chebyshev.psi u + u := by
        rw [abs_of_nonneg (Chebyshev.psi_nonneg _), abs_of_pos hu0]
      _ ≤ Chebyshev.psi B + B := add_le_add (Chebyshev.psi_mono hu.2) hu.2
  simpa only [Ioc_union_Ioi_eq_Ioi (by linarith : (1 : ℝ) ≤ B)] using hlocal.union htail

private lemma relative_chebyshev_error_tendsto :
    Tendsto (fun t : ℝ => (Chebyshev.psi t - t) / t) atTop (𝓝 0) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  have hexp : Tendsto
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -c < 0)
        ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
          Real.tendsto_log_atTop))
  have hmul := hO.mul (isBigO_refl (fun x : ℝ => x⁻¹) atTop)
  have hright : Tendsto
      (fun x : ℝ => (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) * x⁻¹)
      atTop (𝓝 0) := by
    refine hexp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, div_eq_mul_inv] using
    hmul.trans_tendsto hright

/-- The original weighted Mangoldt error converges with exact Euler normalization. -/
theorem E₁Λ_tendsto :
    Tendsto (fun t : ℝ => _root_.Mertens.E₁Λ t) atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
  have htail : Tendsto
      (fun t : ℝ => ∫ u in Ioi t, (Chebyshev.psi u - u) / u ^ 2)
      atTop (𝓝 0) := tendsto_integral_Ioi_zero tendsto_id
  have hid : _root_.Mertens.E₁Λ =ᶠ[atTop]
      (fun t : ℝ => (Chebyshev.psi t - t) / t - Real.eulerMascheroniConstant -
        ∫ u in Ioi t, (Chebyshev.psi u - u) / u ^ 2) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have h := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
      chebyshev_error_kernel_integrable ht
    have ht0 : t ≠ 0 := by linarith
    have hdiv : (Chebyshev.psi t - t) / t = Chebyshev.psi t / t - 1 := by
      rw [sub_div, div_self ht0]
    dsimp [_root_.Mertens.E₁Λ]
    rw [hdiv]
    linarith only [h]
  simpa only [zero_sub, sub_zero] using
    ((relative_chebyshev_error_tendsto.sub tendsto_const_nhds).sub htail).congr' hid.symm

/-- The original real-variable weighted prime error has a finite limit. -/
theorem exists_E₁p_limit :
    ∃ ell : ℝ, Tendsto (fun t : ℝ => _root_.Mertens.E₁p t) atTop (𝓝 ell) := by
  let f : ℕ → ℝ := fun n =>
    if ¬n.Prime then ArithmeticFunction.vonMangoldt n / n else 0
  have hf : Summable f := by
    convert ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
      (0 : ZMod 1) using 1
    funext n
    have hn0 : (n : ZMod 1) = 0 := Subsingleton.elim _ _
    by_cases hn : n.Prime <;>
      simp [f, hn, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator, hn0]
  have hprefix : Tendsto
      (fun x : ℝ => ∑ n ∈ Finset.range (⌊x⌋₊ + 1), f n)
      atTop (𝓝 (∑' n, f n)) :=
    hf.hasSum.tendsto_sum_nat.comp
      (tendsto_atTop_mono (fun x : ℝ => Nat.le_succ ⌊x⌋₊) tendsto_nat_floor_atTop)
  have hresidual : Tendsto
      (fun x : ℝ => _root_.Mertens.E₁Λ x - _root_.Mertens.E₁p x)
      atTop (𝓝 (∑' n, f n)) := by
    refine hprefix.congr (fun x => ?_)
    rw [_root_.Mertens.E₁Λ.sub_E₁p_eq_sum_nonprime,
      Nat.range_succ_eq_Icc_zero,
      ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
    simp [f]
  refine ⟨-Real.eulerMascheroniConstant - ∑' n, f n, ?_⟩
  convert E₁Λ_tendsto.sub hresidual using 1
  ext x
  ring

end
end D5.S3.Weil.Mertens.WeightedPrimeLimit
