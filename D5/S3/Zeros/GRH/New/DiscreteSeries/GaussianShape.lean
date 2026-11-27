/- GID: D5/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/DiscreteSeries/GaussianShape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.DiscreteSeries.GaussianShape. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/DiscreteSeries/GaussianShape.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.DiscreteSeries.MinorExpansion
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen.TailBounds
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Discrete series coefficients near 1 and explicitly large Bessel functions (see
New.DiscreteSeries.RestrictionLemma).

This file: Near 1 the coefficient is explicit phase times real factor, uniform error. -/

open Matrix MeasureTheory Finset Fintype Ring Complex ComplexOrder Norms.L2Operator Norms.Frobenius


variable {n} [Fintype n] {ε} {l : @HCParam n ε} {δ T : ℝ} {L A : ℕ} (w : n → ℤ)
  (X : Matrix n n ℂ)

/-- For an integer vector w and a complex matrix X, the real number ∑_{i,j} |w_i − w_j|·|X_ij|². -/
noncomputable abbrev gapWeightedNormSq := ∑ i, ∑ j, |w i - w j| * ‖X i j‖ ^ 2

lemma sum_norm_lie_coordProj_sq : letI a := ∑ j, |w j|; ∑ t ∈ Ioc (-a) a, ‖⁅coordProj (t ≤ w ·),
    X⁆‖ ^ 2 = gapWeightedNormSq w X ∧
    ∑ t ∈ Ioc (-a) a, (coordProj (t ≤ w ·) * X).trace = ∑ i, (w i + a) * X i i := by
  have := neg_sum_abs_le_and_le_sum_abs w; simp [frobenius_norm_sq_eq_sum, coordProj, lie_def,
    trace, (Ioc ..).sum_comm, ite_sub, sub_ite,
    apply_ite norm, ← Order.lt_add_one_iff]; simp [sum_ite, ← add_mul,
    ← Ico_add_one_add_one_eq_Ioc, -Order.lt_add_one_iff, -Order.add_one_le_iff]
  constructor <;> congr! <;> norm_cast <;> grind

lemma norm_weightMinors_sq_le_exp (k : maxCompactU ε) : ‖weightMinors w k‖ ^ 2 ≤
  (-(gapWeightedNormSq w k / 2)).exp := by
  simp [weightMinors_eq_det_zpow_mul_prod _ _ _ (neg_sum_abs_le_and_le_sum_abs w),
    ← sum_norm_lie_coordProj_sq, sum_div, ← sum_neg_distrib, Real.exp_sum,
    ← prod_pow]; gcongr with t; have ⟨a, b⟩ := isStarProjection_coordProj (t ≤ w ·)
  nth_rw 1 [principalMinor_eq_det, ← coordProj, ← a, mul_assoc, det_one_sub_mul_comm, sq,
    ← norm_star, ← norm_mul,
    ← det_conjTranspose, ← det_mul, (isHermitian_conjTranspose_mul_self _).det_eq_prod_eigenvalues]
  grw [norm_prod, (Real.add_one_le_exp _).trans_eq' (sub_add_cancel ‖_‖ 1)]
  simp [← Real.exp_sum, abs_of_nonneg (eigenvalues_conjTranspose_mul_self_nonneg ..),
    ← real_le_real, ↓← trace_star_mul_self_eq_norm_sq, -conjTranspose_sub]
  erw [← (isHermitian_conjTranspose_mul_self _).trace_eq_sum_eigenvalues]
  simp [lie_def, b.isHermitian.eq, mul_sub, sub_mul, mul_assoc, ← maxCompactU.coe_inv, a.eq,
    (coordProj _).trace_mul_comm, trace_mul_comm _⁻¹ (_ * _)]
  grind

/-- Gaussian shape: let l = 2λ have gap 500n³, |l_a| ≤ L, T ≥ max(1, n², n² log(n+L+1)), 10¹²δT ≤ 1,
‖g−1‖ ≤ δ (Frobenius). Then |ψ_λ(g)/exp tr(diag(Λ) log g) − κ| ≤ κ/10 + e^{−100T} for some κ∈[0,1],
log g = `logOneAdd`(g−1), Λ = `HCParam.lowestKType`.

Discrete series coefficients near 1 and explicitly large Bessel functions. -/
lemma dsCoeff_gaussian_shape [Nonempty n]
    (hg : l.HasLargeGap A) (hL : ∀ a, |l a| ≤ L) {g : USign ε} (hZ : ‖g.1.1
  - 1‖ ≤ δ) (hT : 1 ≤ T) (a : card n ^ 2 ≤ T := by nlinarith) (b : card n ^ 2 * Real.log (card n +
  L + 1) ≤ T := by bound) (hδ : δ * T ≤ 1e-12 := by bound) : ∃ κ ∈ Set.Icc (0 : ℝ) 1, ‖l.dsCoeff g /
  (intDiagonal l.lowestKType * logOneAdd (g.1.1 - 1)).trace.exp - κ‖ ≤ κ / 10 + (-100 * T).exp := by
  obtain ⟨this, ⟨y, y1, y2⟩, H0, t, h⟩ := (norm_nonneg _).trans hZ,
    exists_principalMinor_eq_exp hg g (by nlinarith), kTypeNormSq_pos l.lowestKType,
    (norm_exp_sub_sum_le_exp_norm_sub_sum · 1), measure_ball_le_integral_dsCoeff hL
    (haarK ε) (maxCompactU ε).subtype integrable_of_compactSpace 1 le_rfl
  simp [↓← ENNReal.ofReal_mul', le_of_lt, dsCoeff_of_mem_maxCompactU, unitary, star,
    @CStarRing.norm_of_mem_unitary _ instL2OpNormedRing, ← maxCompactU.coe_inv] at h t
  simp (disch := positivity) [← Real.log_nonneg_iff, Real.log_mul] at h
  repeat grw [Real.log_le_self Nat.ofNat_pos.le] at h
  let q := gapWeightedNormSq (-paramAddRho l) (g - 1) / 4
  use q.exp⁻¹, ⟨by bound, by simp [field]; positivity⟩
  set E := @trace ..
  have d k := by simpa [principalMinor_of_forall, coordProj, lie_def, -det_mul] using (y2 ⊤ · k)
  choose r e hr using fun k : maxCompactU ε ↦ show ∃ r, weightMinors _ _ =
    (q - E - r).exp ∧ ‖r‖ ≤ 1e6 * δ * (q + gapWeightedNormSq l.lowestKType k / 2 + card n ^ 2) by
    choose x f i using fun t ↦
      y2 (t ≤ (-paramAddRho l) ·) (by simp [← hg.paramAddRho_lt_iff]; lia) k
    refine ⟨_, by rw [weightMinors_eq_det_zpow_mul_prod (d k ▸ exp_ne_zero _) _ _
      (neg_sum_abs_le_and_le_sum_abs _), d, funext f,
      ← exp_int_mul, ← exp_sum, ← exp_add, sub_sub_self], ?_⟩
    simp_rw [sum_add_distrib, ← sub_sub, sum_norm_lie_coordProj_sq, ← sum_div, add_mul]
    conv_lhs => enter [1, 1]; simp [lowestKType, E, q, trace, sub_mul, mul_sum,
      ← sum_norm_lie_coordProj_sq]; ring
    grw [norm_sub_le, norm_sum_le, norm_sum_le, i, ← mul_sum, norm_mul_le_of_le (r₁ := card n)
      (mod_cast abs_twoRho_le ..)
      ((norm_logOneAdd_le (hZ.trans (by nlinarith))).trans' (by grw [← sq_le_sq₀,
      frobenius_norm_sq_eq_sum, ← single_le_sum, ← single_le_sum] <;> simp [sum_nonneg'])), hZ,
      sum_add_distrib, (sum_norm_lie_coordProj_sq ..).1, (sum_norm_lie_coordProj_sq ..).1.trans_le
      (c := gapWeightedNormSq l.lowestKType k + 2 * card n * re (k.1.1.1ᴴ *
      k).trace) (by simp [gapWeightedNormSq, trace_star_mul_self_eq_norm_sq,
                      frobenius_norm_sq_eq_sum, mul_sum, ← sum_add_distrib, ← add_mul, -ofReal_pow]
                    gcongr; norm_cast; grind [lowestKType, twoRho])]
    simp [q, ← sub_nonneg, ← maxCompactU.coe_inv]; ring; positivity
  grw [y1, flenstedJensen, div_right_comm, div_sub' (by positivity), norm_div,
    Complex.norm_of_nonneg H0.le,
    div_le_iff₀ H0, ← integral_div, ← integral_complex_ofReal, ← integral_mul_const, ← integral_sub
    (integrable_of_compactSpace (by fun_prop (disch := simp [*]))) integrable_of_compactSpace,
    add_mul, ← integral_const_mul, ← average_const (haarK ε) (_ * _), average_eq_integral,
    ← integral_add integrable_of_compactSpace integrable_of_compactSpace]
  refine norm_integral_le_of_norm_le integrable_of_compactSpace (.of_forall fun k ↦ ?_)
  simp [e, mul_conj', exp_sub]; field_simp
  simp
  by_cases ‖r k‖ < 20⁻¹
  · grw [norm_exp_sub_one_le, ← H0] <;> nlinarith
  grw [← sq_nonneg, zero_add, t, sub_one_lt, norm_weightMinors_sq_le_exp, ← Real.exp_log H0]
  field
  simp [← Real.exp_add]
  nlinarith [hr k, le_mul_of_one_le_right this hT]
