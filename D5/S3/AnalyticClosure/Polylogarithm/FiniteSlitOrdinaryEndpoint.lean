/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitOrdinaryEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed finite prefixes and the exact endpoint sum of ordinary inverse coefficients. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryCoefficients
import Mathlib.Analysis.Complex.AbelLimit
import D5.S3.AnalyticClosure.PositiveSeriesTail

/-! Absolute summability from the actual radial endpoint and a negative coefficient tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators

namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint

/-- The real endpoint of the actual normalized reciprocal. -/
def endpoint (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) : ℝ :=
  if 1 < (head : ℕ) then (CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) else 0

private theorem signed_endpoint (a : ℕ → ℝ) (A : ℝ → ℝ) (L : ℝ)
    (hs : ∀ r : ℝ, 0 ≤ r → r < 1 → HasSum (fun n ↦ a n * r ^ n) (A r))
    (hlim : Tendsto A (𝓝[<] 1) (𝓝 L))
    (hneg : ∀ᶠ n : ℕ in atTop, a n < 0) :
    Summable (fun n ↦ |a n|) ∧ HasSum a L := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hneg
  let q : ℕ → ℝ := fun n ↦ -a (n + N)
  let P : ℝ → ℝ := fun r ↦ ∑ i ∈ Finset.range N, a i * r ^ i
  have hqpos (n : ℕ) : 0 ≤ q n := (neg_pos.mpr (hN (n + N) (Nat.le_add_left N n))).le
  have hP : Tendsto P (𝓝[<] 1) (𝓝 (P 1)) := by
    have hcont : Continuous P := by dsimp [P]; fun_prop
    exact (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hbound (m : ℕ) : ∑ i ∈ Finset.range m, q i ≤ P 1 - L := by
    have hleft : Tendsto (fun r : ℝ ↦ ∑ i ∈ Finset.range m, q i * r ^ (i + N))
        (𝓝[<] 1) (𝓝 (∑ i ∈ Finset.range m, q i)) := by
      have hcont : Continuous (fun r : ℝ ↦ ∑ i ∈ Finset.range m, q i * r ^ (i + N)) := by
        fun_prop
      simpa only [one_pow, mul_one] using
        (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hleft (hP.sub hlim)
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have htail : HasSum (fun n : ℕ ↦ a (n + N) * r ^ (n + N)) (A r - P r) :=
      (hasSum_nat_add_iff' N).mpr (hs r hr.1.le hr.2)
    have htail' : HasSum (fun n : ℕ ↦ q n * r ^ (n + N)) (P r - A r) := by
      simpa only [q, neg_mul, neg_sub] using htail.neg
    have hle := htail'.summable.sum_le_tsum (Finset.range m)
      (fun n _ ↦ mul_nonneg (hqpos n) (pow_nonneg hr.1.le _))
    rwa [htail'.tsum_eq] at hle
  have hqs : Summable q := summable_of_sum_range_le hqpos hbound
  have has : Summable a := (summable_nat_add_iff N).mp (by
    simpa only [q, neg_neg] using hqs.neg)
  have hAbel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt has.hasSum.tendsto_sum_nat
  have heq : (fun r : ℝ ↦ ∑' n : ℕ, a n * r ^ n) =ᶠ[𝓝[<] 1] A := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    exact (hs r hr.1.le hr.2).tsum_eq
  have hsum : (∑' n, a n) = L := tendsto_nhds_unique (hAbel.congr' heq) hlim
  exact ⟨has.abs, hsum ▸ has.hasSum⟩

private theorem radial_endpoint (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    Tendsto (fun r : ℝ ↦ (FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re)
      (𝓝[<] 1) (𝓝 (endpoint head tail ell)) := by
  obtain ⟨ρ, _hρ, _hρ1, _hn, hlim, _rest⟩ := CompositionBanks.result head tail ell
  have hmap : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[<] 1)
      (𝓝[CompositionContinuation.omega] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 1 - (r : ℂ) ∈ Complex.slitPlane
      rw [Complex.mem_slitPlane_iff]
      left
      simpa using sub_pos.mpr (show r < 1 from hr)
  have heq : (fun r : ℝ ↦ FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)) =ᶠ[𝓝[<] 1]
      (fun r : ℝ ↦ ((r : ℂ) ^ CompositionDisk.depth tail /
        CompositionContinuation.continued (head :: tail) (r : ℂ)) ^ (ell : ℕ)) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.1.ne'
    simp only [FiniteSlitCompositionMoments.reciprocal,
      CompositionZeroFreeCollar.normalizedContinuation, if_neg hn, inv_div]
  have hactual : Tendsto
      (fun r : ℝ ↦ FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ))
      (𝓝[<] 1) (𝓝 ((endpoint head tail ell : ℝ) : ℂ)) := by
    simpa only [endpoint, apply_ite, Complex.ofReal_pow, Complex.ofReal_inv,
      Complex.ofReal_zero] using (hlim.comp hmap).congr' heq.symm
  simpa only [Function.comp_def, Complex.ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp hactual

private theorem strict_partial (a : ℕ → ℝ) (L : ℝ) (hs : HasSum a L)
    (hneg : ∀ᶠ n : ℕ in atTop, a n < 0) :
    ∀ᶠ n : ℕ in atTop, L < ∑ i ∈ Finset.range (n + 1), a i := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hneg
  filter_upwards [eventually_ge_atTop N] with n hn
  have htail : HasSum (fun m : ℕ ↦ a (m + (n + 1)))
      (L - ∑ i ∈ Finset.range (n + 1), a i) :=
    (hasSum_nat_add_iff' (n + 1)).mpr hs
  have hp (m : ℕ) : 0 < -a (m + (n + 1)) := neg_pos.mpr (hN _ (by omega))
  have hlt := D5.S3.AnalyticClosure.PositiveSeriesTail.finite_partial_sum_lt_tsum_of_pos_outside
    (fun m : ℕ ↦ -a (m + (n + 1))) ∅ (fun m ↦ (hp m).le)
    htail.neg.summable ⟨0, by simp, hp 0⟩
  simp only [Finset.sum_empty] at hlt
  rw [htail.neg.tsum_eq] at hlt
  linarith

/-- Absolute summability and the exact total retain the whole signed finite prefix. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) :
    Summable (fun n : ℕ ↦ |PowerSeries.coeff n
      (FiniteSlitOrdinaryCoefficients.ordinary head tail ell)|) ∧
    HasSum (fun n : ℕ ↦ PowerSeries.coeff n
      (FiniteSlitOrdinaryCoefficients.ordinary head tail ell)) (endpoint head tail ell) ∧
    (∀ᶠ n : ℕ in atTop, endpoint head tail ell <
      ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff i
        (FiniteSlitOrdinaryCoefficients.ordinary head tail ell)) := by
  obtain ⟨_hc, hs, hneg⟩ := FiniteSlitOrdinaryCoefficients.result head tail ell
  have hreal (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) : HasSum
      (fun n : ℕ ↦ PowerSeries.coeff n
        (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) * r ^ n)
      (FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re := by
    have hrc : ‖(r : ℂ)‖ < 1 := by
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    have h := Complex.reCLM.hasSum (hs (r : ℂ) hrc)
    simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, ← Complex.ofReal_pow, mul_zero, sub_zero] using h
  obtain ⟨habs, htotal⟩ := signed_endpoint _ _ _ hreal (radial_endpoint head tail ell) hneg
  exact ⟨habs, htotal, strict_partial _ _ htotal hneg⟩

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint
