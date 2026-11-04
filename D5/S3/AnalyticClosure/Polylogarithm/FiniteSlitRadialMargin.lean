/- GID: D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/FiniteSlitRadialMargin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Quantitative radial margin of the original admissible reciprocal. -/

import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint

/-! The strictly positive first source coefficient gives a quantitative admissible margin. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators
namespace D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin

private theorem inverse_power_gap (x Z : ℝ) (hx : 0 < x) (hxZ : x ≤ Z) (k : ℕ) :
    (Z - x) / Z ^ 2 * Z⁻¹ ^ k ≤ x⁻¹ ^ (k + 1) - Z⁻¹ ^ (k + 1) := by
  have hZ : 0 < Z := hx.trans_le hxZ
  have hi : Z⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hZ hx).mpr hxZ
  have hpow : Z⁻¹ ^ k ≤ x⁻¹ ^ k := pow_le_pow_left₀ (inv_nonneg.mpr hZ.le) hi k
  have hgap : (Z - x) / Z ^ 2 ≤ x⁻¹ - Z⁻¹ := by
    apply (div_le_iff₀ (pow_pos hZ 2)).mpr
    field_simp
    nlinarith [sq_nonneg (Z - x)]
  have hmul := mul_le_mul_of_nonneg_right hgap (pow_nonneg (inv_nonneg.mpr hZ.le) k)
  have hmul' := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr hx.le)
  calc
    (Z - x) / Z ^ 2 * Z⁻¹ ^ k ≤ (x⁻¹ - Z⁻¹) * Z⁻¹ ^ k := hmul
    _ ≤ x⁻¹ * x⁻¹ ^ k - Z⁻¹ * Z⁻¹ ^ k := by nlinarith [hmul']
    _ = x⁻¹ ^ (k + 1) - Z⁻¹ ^ (k + 1) := by simp only [pow_succ]; ring

/-- For every admissible composition and positive reciprocal power the actual
radial quotient has a uniform strictly positive lower bound near one. -/
theorem result (head : ℕ+) (tail : List ℕ+) (ell : ℕ+) (hh : 1 < (head : ℕ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1,
      c ≤ ((FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re -
        FiniteSlitOrdinaryEndpoint.endpoint head tail ell) / (1 - r) := by
  let f := CompositionDisk.coefficient head tail
  let Z := CompositionBoundary.zeta head tail
  obtain ⟨hf, _hw, hfZ, hZ, _⟩ := CompositionBoundary.result head tail hh
  change Summable f at hf
  change (∑' n, f n) = Z at hfZ
  change 0 < Z at hZ
  have hfp (n : ℕ) : 0 < f n := (CompositionDisk.source_series head tail).1 n
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt ell.pos)
  have hf1 := hfp 1
  let c := f 1 / Z ^ 2 * Z⁻¹ ^ k
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hfr : Summable (fun n ↦ f n * r ^ n) := Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (hfp n).le (pow_nonneg hr.1.le n))
    (fun n ↦ mul_le_of_le_one_right (hfp n).le (pow_le_one₀ hr.1.le hr.2.le)) hf
  let x := ∑' n : ℕ, f n * r ^ n
  have hx : 0 < x := by
    have hle := hfr.sum_le_tsum {0}
      (fun n _ ↦ mul_nonneg (hfp n).le (pow_nonneg hr.1.le n))
    have hle' : f 0 ≤ x := by simpa only [Finset.sum_singleton, pow_zero, mul_one, x] using hle
    exact (hfp 0).trans_le hle'
  have hxZ : x ≤ Z := by
    rw [← hfZ]
    exact hfr.tsum_le_tsum
      (fun n ↦ mul_le_of_le_one_right (hfp n).le (pow_le_one₀ hr.1.le hr.2.le)) hf
  have hdiff : Summable (fun n ↦ f n - f n * r ^ n) := hf.sub hfr
  have hgap : f 1 * (1 - r) ≤ Z - x := by
    have hle := hdiff.sum_le_tsum {1} (fun n _ ↦ sub_nonneg.mpr
      (mul_le_of_le_one_right (hfp n).le (pow_le_one₀ hr.1.le hr.2.le)))
    rw [hf.tsum_sub hfr] at hle
    simpa only [Finset.sum_singleton, pow_one, hfZ, x, mul_sub, mul_one] using hle
  have hrc : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1] using hr.2
  have hnorm : CompositionDisk.normalized head tail (r : ℂ) = (x : ℂ) := by
    have hreal := Complex.ofRealCLM.hasSum hfr.hasSum
    have hs := ((CompositionDisk.source_series head tail).2.2.1 (r : ℂ) hrc).of_norm.hasSum
    apply HasSum.unique hs
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_pow, f, x]
      using hreal
  have hA : (FiniteSlitCompositionMoments.reciprocal head tail ell (r : ℂ)).re =
      x⁻¹ ^ (k + 1) := by
    rw [FiniteSlitCompositionMoments.reciprocal,
      (CompositionZeroFreeCollar.result head tail).1 _ hrc, hnorm, hk]
    simp only [← Complex.ofReal_inv, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hA, FiniteSlitOrdinaryEndpoint.endpoint, if_pos hh, hk]
  apply (le_div_iff₀ (sub_pos.mpr hr.2)).mpr
  have h1 := inverse_power_gap x Z hx hxZ k
  have h2 : c * (1 - r) ≤ (Z - x) / Z ^ 2 * Z⁻¹ ^ k := by
    dsimp [c]
    have hd := (div_le_div_of_nonneg_right hgap (pow_nonneg hZ.le 2))
    have hm := mul_le_mul_of_nonneg_right hd (pow_nonneg (inv_nonneg.mpr hZ.le) k)
    convert hm using 1 <;> ring
  exact h2.trans h1

end D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin
