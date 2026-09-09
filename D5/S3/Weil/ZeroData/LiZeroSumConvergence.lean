/- GID: D5/S3/Weil/ZeroData/LiZeroSumConvergence
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/LiZeroSumConvergence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute real Li summability and conjugate-paired spectral, height, and radial limits. -/

import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZeroData.LiZeroSumConvergence

open Filter
open scoped ComplexConjugate
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

noncomputable section

private theorem reciprocal_weight_summable (Z : ZeroData) :
    Summable (fun k : ℕ =>
      (Z.multiplicity k : ℝ) / (1 + Complex.normSq (Z.gamma k))) := by
  have h := (zeroEquiv Z).summable_iff.mpr (Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam)
  refine h.congr fun k => ?_
  change (Zeta23.zeroMult (Z.zero k) : ℝ) /
    (1 + Complex.normSq (Zeta23.gammaOf (Z.zero k))) = _
  rw [← multiplicity_eq_zeroMult, gammaOf_eq_spectralParameter]
  rfl

private theorem power_real_cancellation (u : ℂ) (hu : ‖u‖ ≤ 1)
    (hre : |u.re| ≤ ‖u‖ ^ 2) (n : ℕ) :
    ‖(1 - u) ^ n - 1‖ ≤ ((2 : ℝ) ^ n - 1) * ‖u‖ ∧
      |1 - ((1 - u) ^ n).re| ≤ ((2 : ℝ) ^ n - 1) * ‖u‖ ^ 2 := by
  have hw : ‖1 - u‖ ≤ 2 := (norm_sub_le 1 u).trans (by
    simpa using (by linarith : 1 + ‖u‖ ≤ 2))
  have hp (m : ℕ) : 0 ≤ (2 : ℝ) ^ m - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by norm_num))
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : (1 - u) ^ (n + 1) - 1 = ((1 - u) ^ n - 1) * (1 - u) - u := by
      rw [pow_succ]; ring
    have hnorm : ‖(1 - u) ^ (n + 1) - 1‖ ≤
        (((2 : ℝ) ^ n - 1) * ‖u‖) * 2 + ‖u‖ := by
      rw [heq]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      exact add_le_add (mul_le_mul ih.1 hw (norm_nonneg _)
        (mul_nonneg (hp n) (norm_nonneg _))) le_rfl
    have heqre : 1 - ((1 - u) ^ (n + 1)).re =
        (1 - ((1 - u) ^ n).re) + u.re + (((1 - u) ^ n - 1) * u).re := by
      rw [pow_succ]
      simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im]
      ring
    have hreal : |1 - ((1 - u) ^ (n + 1)).re| ≤
        ((2 : ℝ) ^ n - 1) * ‖u‖ ^ 2 + ‖u‖ ^ 2 +
          (((2 : ℝ) ^ n - 1) * ‖u‖) * ‖u‖ := by
      rw [heqre]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact (abs_add_le _ _).trans (add_le_add ih.2 hre)
      · exact (Complex.abs_re_le_norm _).trans (by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right ih.1 (norm_nonneg _))
    constructor
    · calc
        _ ≤ _ := hnorm
        _ = _ := by rw [pow_succ]; ring
    · calc
        _ ≤ _ := hreal
        _ = _ := by rw [pow_succ]; ring

private theorem gamma_normSq (Z : ZeroData) (k : ℕ) :
    Complex.normSq (Z.gamma k) = Complex.normSq (Z.zero k) - (Z.zero k).re + 1 / 4 := by
  simp [ZeroData.gamma, spectralParameter, Complex.normSq_apply,
    D5.S3.Weil.Convention.criticalAbscissa]
  ring

private theorem li_zero_real_tail_bound (Z : ZeroData) (n k : ℕ)
    (hk : 2 ≤ ‖Z.gamma k‖) :
    |(Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re)| ≤
      (4 * (2 : ℝ)^n) *
        ((Z.multiplicity k : ℝ) / (1 + Complex.normSq (Z.gamma k))) := by
  have hz := Z.zero_isNontrivial k
  have hx : 0 < (Z.zero k).re ∧ (Z.zero k).re < 1 := hz.2
  have hg : 4 ≤ Complex.normSq (Z.gamma k) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (Z.gamma k)]
  have hq : 1 ≤ Complex.normSq (Z.zero k) := by
    rw [gamma_normSq] at hg
    linarith
  have hqp : 0 < Complex.normSq (Z.zero k) := lt_of_lt_of_le (by norm_num) hq
  have hn : 1 ≤ ‖Z.zero k‖ := by
    rw [Complex.normSq_eq_norm_sq] at hq
    nlinarith [norm_nonneg (Z.zero k)]
  have hu : ‖(Z.zero k)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hn
  have hre : |((Z.zero k)⁻¹).re| ≤ ‖(Z.zero k)⁻¹‖ ^ 2 := by
    rw [Complex.inv_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_inv,
      abs_of_nonneg (div_nonneg hx.1.le hqp.le), inv_eq_one_div]
    exact div_le_div_of_nonneg_right hx.2.le hqp.le
  have hb := (power_real_cancellation ((Z.zero k)⁻¹) hu hre n).2
  have hd : 1 + Complex.normSq (Z.gamma k) ≤ 4 * Complex.normSq (Z.zero k) := by
    rw [gamma_normSq]
    linarith
  have hdp : 0 < 1 + Complex.normSq (Z.gamma k) := by positivity
  have hinv : (Complex.normSq (Z.zero k))⁻¹ ≤
      4 / (1 + Complex.normSq (Z.gamma k)) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hqp hdp]
    simpa [mul_comm] using hd
  have hb' : |1 - ((1 - 1 / Z.zero k) ^ n).re| ≤
      (2 : ℝ) ^ n * (4 / (1 + Complex.normSq (Z.gamma k))) := by
    simp only [one_div] at *
    calc
      _ ≤ ((2 : ℝ) ^ n - 1) * ‖(Z.zero k)⁻¹‖ ^ 2 := hb
      _ ≤ (2 : ℝ) ^ n * ‖(Z.zero k)⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ _ := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_inv]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (Z.multiplicity k : ℝ) *
        ((2 : ℝ) ^ n * (4 / (1 + Complex.normSq (Z.gamma k)))) :=
      mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg _)
    _ = _ := by ring

/-- For every presentation of the actual nontrivial zeta zeros, the real Li series
is absolutely summable, with the exact analytic multiplicities. -/
theorem li_zero_real_summable (Z : ZeroData) (n : ℕ) :
    Summable (fun k : ℕ =>
      (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re)) := by
  refine Summable.of_norm_bounded_eventually
    ((reciprocal_weight_summable Z).mul_left (4 * (2 : ℝ) ^ n)) ?_
  filter_upwards [(Z.symmetricIndices 2).finite_toSet.compl_mem_cofinite] with k hk
  have hk' : 2 ≤ ‖Z.gamma k‖ := by
    have hlt : 2 < ‖Z.gamma k‖ := by simpa using hk
    exact hlt.le
  simpa only [Real.norm_eq_abs] using li_zero_real_tail_bound Z n k hk'

private theorem gamma_norm (Z : ZeroData) (k : ℕ) :
    ‖Z.gamma k‖ = ‖Z.zero k - (1 / 2 : ℂ)‖ := by
  simp [ZeroData.gamma, spectralParameter, D5.S3.Weil.Convention.criticalAbscissa]

private theorem mem_height_cutoff (Z : ZeroData) (T : ℝ) (k : ℕ) :
    k ∈ (Z.symmetricIndices (T + 1)).filter (fun j => |(Z.zero j).im| ≤ T) ↔
      |(Z.zero k).im| ≤ T := by
  classical
  rw [Finset.mem_filter, Z.mem_symmetricIndices]
  refine and_iff_right_of_imp fun h => ?_
  rw [gamma_norm]
  have hx := (Z.zero_isNontrivial k).2
  have hx' : |(Z.zero k).re - 1 / 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ |(Z.zero k - (1 / 2 : ℂ)).re| + |(Z.zero k - (1 / 2 : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ T + 1 := by
      simp only [Complex.sub_re, Complex.sub_im]
      norm_num
      linarith

private theorem mem_radial_cutoff (Z : ZeroData) (T : ℝ) (k : ℕ) :
    k ∈ (Z.symmetricIndices (T + 1)).filter (fun j => ‖Z.zero j‖ ≤ T) ↔
      ‖Z.zero k‖ ≤ T := by
  classical
  rw [Finset.mem_filter, Z.mem_symmetricIndices]
  refine and_iff_right_of_imp fun h => ?_
  rw [gamma_norm]
  calc
    _ ≤ ‖Z.zero k‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ T + 1 := by norm_num; linarith

private theorem cutoff_exhaustion (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (s : ℝ → Finset ℕ) (hs : ∀ T k, k ∈ s T ↔ f k ≤ T) :
    Tendsto s atTop atTop := by
  rw [tendsto_atTop]
  intro a
  filter_upwards [eventually_ge_atTop (∑ k ∈ a, f k)] with T hT
  intro k hk
  rw [hs]
  exact (Finset.single_le_sum (fun j _ => hf j) hk).trans hT

private theorem paired_sum (Z : ZeroData) (n : ℕ) (s : Finset ℕ)
    (hs : ∀ k, Z.conjugation k ∈ s ↔ k ∈ s) :
    (∑ k ∈ s, (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n)) =
      ((∑ k ∈ s, (Z.multiplicity k : ℝ) *
        (1 - ((1 - 1 / Z.zero k) ^ n).re) : ℝ) : ℂ) := by
  have hc : conj (∑ k ∈ s, (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n)) =
      ∑ k ∈ s, (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n) := by
    rw [map_sum]
    refine Finset.sum_equiv Z.conjugation (fun k => (hs k).symm) ?_
    intro k _
    simp [Z.multiplicity_conjugation, Z.zero_conjugation]
  have hr := (Complex.conj_eq_iff_re.mp hc).symm
  convert hr using 1
  congr 1
  simp

private theorem paired_cutoff_limit (Z : ZeroData) (n : ℕ) (s : ℝ → Finset ℕ)
    (hs : ∀ T k, Z.conjugation k ∈ s T ↔ k ∈ s T)
    (ht : Tendsto s atTop atTop) :
    Tendsto (fun T : ℝ => ∑ k ∈ s T,
        (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n))
      atTop (nhds ((∑' k : ℕ, (Z.multiplicity k : ℝ) *
        (1 - ((1 - 1 / Z.zero k) ^ n).re) : ℝ) : ℂ)) := by
  simpa only [Function.comp_def, paired_sum Z n _ (hs _)] using
    (Complex.continuous_ofReal.tendsto _).comp ((li_zero_real_summable Z n).hasSum.comp ht)

/-- Spectral balls, absolute-height cutoffs, and zero-modulus cutoffs have the
same Li limit. Every finite sum is conjugation invariant; no absolute summability
of the unpaired complex terms is asserted. -/
theorem li_zero_cutoff_limits (Z : ZeroData) (n : ℕ) :
  (Tendsto (fun T : ℝ => ∑ k ∈ Z.symmetricIndices T, (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n))
    atTop (nhds ((∑' k : ℕ, (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re) : ℝ) : ℂ))) ∧
  (Tendsto (fun T : ℝ => ∑ k ∈ (Z.symmetricIndices (T + 1)).filter
      (fun k => |(Z.zero k).im| ≤ T), (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n))
    atTop (nhds ((∑' k : ℕ, (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re) : ℝ) : ℂ))) ∧
  (Tendsto (fun T : ℝ => ∑ k ∈ (Z.symmetricIndices (T + 1)).filter
      (fun k => ‖Z.zero k‖ ≤ T), (Z.multiplicity k : ℂ) * (1 - (1 - 1 / Z.zero k) ^ n))
    atTop (nhds ((∑' k : ℕ, (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re) : ℝ) : ℂ))) := by
  classical
  refine ⟨paired_cutoff_limit Z n _ (fun _ _ => Z.conjugation_mem_symmetricIndices)
    (tendsto_symmetricIndices Z), ?_, ?_⟩
  · apply paired_cutoff_limit
    · intro T k
      simp only [mem_height_cutoff, Z.zero_conjugation, Complex.conj_im, abs_neg]
    · exact cutoff_exhaustion (fun k => |(Z.zero k).im|) (fun k => abs_nonneg _) _
        (mem_height_cutoff Z)
  · apply paired_cutoff_limit
    · intro T k
      simp only [mem_radial_cutoff, Z.zero_conjugation, Complex.norm_conj]
    · exact cutoff_exhaustion (fun k => ‖Z.zero k‖) (fun k => norm_nonneg _) _
        (mem_radial_cutoff Z)

private theorem real_sum_presentation_eq (Z Z' : ZeroData) (n : ℕ) :
    (∑' k : ℕ, (Z.multiplicity k : ℝ) * (1 - ((1 - 1 / Z.zero k) ^ n).re)) =
      ∑' k : ℕ, (Z'.multiplicity k : ℝ) * (1 - ((1 - 1 / Z'.zero k) ^ n).re) := by
  let f : {rho : ℂ // Zeta23.IsNontrivialZero rho} → ℝ := fun rho =>
    (Zeta23.zeroMult rho : ℝ) * (1 - ((1 - 1 / (rho : ℂ)) ^ n).re)
  have he (W : ZeroData) : (∑' k : ℕ, (W.multiplicity k : ℝ) *
      (1 - ((1 - 1 / W.zero k) ^ n).re)) = ∑' rho, f rho := by
    rw [← (zeroEquiv W).tsum_eq f]
    apply tsum_congr
    intro k
    change (W.multiplicity k : ℝ) * _ = (Zeta23.zeroMult (W.zero k) : ℝ) * _
    rw [multiplicity_eq_zeroMult]
    rfl
  exact (he Z).trans (he Z').symm

#print axioms li_zero_real_summable
#print axioms li_zero_cutoff_limits
#print axioms li_zero_real_tail_bound
#print axioms real_sum_presentation_eq

end
end D5.S3.Weil.ZeroData.LiZeroSumConvergence
