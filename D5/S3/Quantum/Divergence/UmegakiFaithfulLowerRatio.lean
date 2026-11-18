/- GID: D5/S3/Quantum/Divergence/UmegakiFaithfulLowerRatio
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiFaithfulLowerRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Faithful flagged density pairs approximate the inverse-weighted channel ratio. -/

import D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
import D5.S3.Quantum.Divergence.UmegakiBKMPath
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

/-! Actual faithful density-pair approximation via ordered rare-flag and local limits.

The public approximation result constructs the actual state witnesses with an
earned positive denominator. Private lemmas provide consumed analytic estimates
and transport support; none is a separate delivery. The uniform floor in
`affine_floor` and compact-interval estimate in `average_limit` feed the
construction, normalization and ordered parameter selection on the live
proof path of `faithful_density_pair_ratio_approx`.
proof_shape: content; admission_basis: escape-witness.
escape_witness: the public theorem's construction of actual faithful density
pairs from the ordered limits, with a strictly positive input divergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open D5.S3.Divergence.LogDerivTrace
open D5.S3.Divergence.AudenaertBinaryHolevoBound
open D5.S3.Quantum.Divergence.UmegakiBKMPath
open D5.S3.Quantum.Divergence.UmegakiRareFlagBKM
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

namespace D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio

universe ur ua ub
variable {r : Type ur} {a : Type ua} {b : Type ub} [Fintype r] [DecidableEq r]
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

private def reindexStar (e : a ≃ b) : Matrix a a ℂ ≃⋆ₐ[ℝ] Matrix b b ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℝ ℂ e) (by
    intro X
    ext i j
    rfl)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma reindex_log (e : a ≃ b) (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    reindexStar e (CFC.log X) = CFC.log (reindexStar e X) := by
  have hE : Continuous (reindexStar e) :=
    (Matrix.reindexLinearEquiv ℝ ℂ e e).toContinuousLinearEquiv.continuous
  exact StarAlgHomClass.map_cfc (reindexStar e) Real.log X
    (X.finite_real_spectrum.continuousOn _) hE hX
    (hX.submatrix e.symm)

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma reindex_logDeriv (e : a ≃ b) (Z H : Matrix a a ℂ) :
    reindexStar e (logDeriv Z H) = logDeriv (reindexStar e Z) (reindexStar e H) := by
  let E := (Matrix.reindexLinearEquiv ℝ ℂ e e).toContinuousLinearEquiv
  have hi (X : Matrix a a ℂ) : reindexStar e X⁻¹ = (reindexStar e X)⁻¹ := by
    exact (Matrix.inv_reindex e e X).symm
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  change E (∫ t in Set.Ioi (0 : ℝ), (Z+t • 1)⁻¹ * H * (Z+t • 1)⁻¹) = _
  rw [← E.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards [] with t
  change reindexStar e (_ * H * _) = _
  simp only [map_mul, hi, map_add, map_smul, map_one]

private def d (A B : Matrix a a ℂ) : ℝ :=
  (A * (CFC.log A - CFC.log B)).trace.re

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private def localIntegral (B H : Matrix a a ℂ) (e : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1-t) * (H * logDeriv (B+(t*e) • H) H).trace.re

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma affine_floor {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.PosDef) (hH : H.IsHermitian) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧
      ∀ s : ℝ, |s| < r → c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ B+s • H := by
  obtain ⟨c, hc, hcB, _⟩ := common_floor B B hB hB
  refine ⟨c/2, c/(2*(‖H‖+1)), by positivity, by positivity, ?_⟩
  intro s hs
  have hn : ‖s • H‖ ≤ c/2 := by
    rw [norm_smul, Real.norm_eq_abs]
    have h := (lt_div_iff₀ (show 0 < 2*(‖H‖+1) by positivity)).mp hs
    nlinarith [norm_nonneg H, abs_nonneg s]
  have hl : -(‖s • H‖ • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ s • H := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      ((IsSelfAdjoint.all s).smul hH.isSelfAdjoint).neg_algebraMap_norm_le_self
  have hsmall : -(c/2) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ s • H := by
    have hh : -(c/2) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ -(‖s • H‖ • 1) := by
      simpa only [neg_smul] using
        neg_le_neg (smul_le_smul_of_nonneg_right hn (zero_le_one :
          (0 : Matrix (Fin n) (Fin n) ℂ) ≤ 1))
    exact hh.trans hl
  calc
    (c/2) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        c • (1 : Matrix (Fin n) (Fin n) ℂ) + -(c/2) • 1 := by module
    _ ≤ B+s • H := add_le_add hcB hsmall

set_option maxHeartbeats 1000000 in
private lemma average_limit (Q : ℝ → ℝ) (hQ : ContinuousAt Q 0)
    (hi : ∀ᶠ e : ℝ in 𝓝 0,
      IntervalIntegrable (fun t : ℝ => (1-t)*Q (t*e)) volume 0 1) :
    Tendsto (fun e : ℝ => ∫ t in (0 : ℝ)..1, (1-t)*Q (t*e))
      (𝓝 0) (𝓝 (Q 0 / 2)) := by
  have hc : IntervalIntegrable (fun t : ℝ => (1-t)*Q 0) volume 0 1 := by
    exact (by fun_prop : Continuous (fun t : ℝ => (1-t)*Q 0)).intervalIntegrable _ _
  have hv : (∫ t in (0 : ℝ)..1, (1-t)*Q 0) = Q 0/2 := by
    rw [intervalIntegral.integral_mul_const]
    have hh : (∫ t in (0 : ℝ)..1, 1-t) = (1:ℝ)/2 := by
      rw [intervalIntegral.integral_sub (f := fun _ => (1:ℝ)) (g := fun t : ℝ => t)
        intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)]
      norm_num [integral_id]
    rw [hh]
    ring
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨v, hvp, hvQ⟩ := Metric.continuousAt_iff.mp hQ (η/2) (by positivity)
  filter_upwards [hi, Metric.ball_mem_nhds (0 : ℝ) hvp] with e he hev
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hev
  rw [Real.dist_eq, ← hv, ← intervalIntegral.integral_sub he hc]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(1-t)*Q (t*e) - (1-t)*Q 0‖ ≤ η/2 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have habs : |t*e| < v := by
      rw [abs_mul, abs_of_nonneg ht.1.le]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg e)).trans_lt (by simpa using hev)
    have hh := hvQ (by simpa only [Real.dist_eq, sub_zero] using habs)
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact (mul_le_mul_of_nonneg_left hh.le (sub_nonneg.mpr ht.2)).trans
      (by nlinarith [ht.1])
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hh' : |∫ t in (0 : ℝ)..1, (1-t)*Q (t*e) - (1-t)*Q 0| ≤ η/2 := by
    simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh
  exact hh'.trans_lt (by linarith)

set_option maxHeartbeats 1000000 in
attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma local_data_fin {n : ℕ} (B H : Matrix (Fin n) (Fin n) ℂ)
    (hB : B.PosDef) (hH : H.IsHermitian) (ht : H.trace = 0) :
    Tendsto (localIntegral B H) (𝓝 0)
      (𝓝 ((H * logDeriv B H).trace.re / 2)) ∧
    ∀ᶠ e : ℝ in 𝓝 0, (B+e • H).PosDef ∧
      d (B+e • H) B = e^2 * localIntegral B H e := by
  obtain ⟨c, r, hc, hr, hfloor⟩ := affine_floor B H hB hH
  let Q : ℝ → ℝ := fun s => (H * logDeriv (B+s • H) H).trace.re
  have hcont : ContinuousOn Q (Set.Ioo (-r) r) := by
    let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
      Complex.reCLM.comp ((Matrix.traceLinearMap (Fin n) ℝ ℂ).toContinuousLinearMap.comp
        (mulLeftLinearMap (Fin n) ℝ H).toContinuousLinearMap)
    exact L.continuous.comp_continuousOn
      (continuousOn_logDeriv_of_floor B H _ c hc (fun s hs =>
        hfloor s (abs_lt.mpr hs)))
  have hQ : ContinuousAt Q 0 :=
    (hcont 0 (by constructor <;> linarith)).continuousAt
      (isOpen_Ioo.mem_nhds (by constructor <;> linarith))
  have hi : ∀ᶠ e : ℝ in 𝓝 0,
      IntervalIntegrable (fun t : ℝ => (1-t)*Q (t*e)) volume 0 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have hmap (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : t*e ∈ Set.Ioo (-r) r := by
      apply abs_lt.mp
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg e)).trans_lt (by simpa using he)
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuous_const.sub continuous_id).continuousOn.mul
      (hcont.comp (by fun_prop) hmap)
  refine ⟨?_, ?_⟩
  · unfold localIntegral
    simpa only [Q, zero_mul, zero_smul, add_zero] using average_limit Q hQ hi
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have hp : (B+e • H).PosDef :=
      ((IsStrictlyPositive.smul hc isStrictlyPositive_one).of_le (hfloor e he)).posDef
    refine ⟨hp, ?_⟩
    have heq : (B+e • H)-B = e • H := by module
    have hh := relativeEntropy_eq_integral_bkm (B+e • H) B hp hB
    rw [heq] at hh
    simp only [Matrix.trace_smul, ht, smul_zero, Complex.zero_re, sub_zero] at hh
    change d (B+e • H) B = _ at hh
    rw [hh, localIntegral, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [smul_smul, show t*e = t*e from rfl, logDeriv_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring

set_option maxHeartbeats 1000000 in
attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma local_data (B H : Matrix a a ℂ)
    (hB : B.PosDef) (hH : H.IsHermitian) (ht : H.trace = 0) :
    Tendsto (localIntegral B H) (𝓝 0)
      (𝓝 ((H * logDeriv B H).trace.re / 2)) ∧
    ∀ᶠ e : ℝ in 𝓝 0, (B+e • H).PosDef ∧
      d (B+e • H) B = e^2 * localIntegral B H e := by
  let e := Fintype.equivFin a
  let E := reindexStar e
  have hd := local_data_fin (E B) (E H)
    (hB.submatrix e.symm.injective) (hH.submatrix e.symm)
    ((trace_reindex e H).trans ht)
  have hI : localIntegral (E B) (E H) = localIntegral B H := by
    funext s
    unfold localIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    have hh := reindex_logDeriv e (B+(t*s) • H) H
    change E (logDeriv _ H) = _ at hh
    rw [map_add, map_smul] at hh
    rw [← hh, ← map_mul, show ∀ X, (E X).trace = X.trace from trace_reindex e]
  have hq : ((E H) * logDeriv (E B) (E H)).trace = (H * logDeriv B H).trace := by
    rw [← reindex_logDeriv, ← map_mul]
    exact trace_reindex e _
  refine ⟨by simpa only [hI, hq] using hd.1, ?_⟩
  filter_upwards [hd.2] with s hs
  have hp : (B+s • H).PosDef := by
    have hh := hs.1.submatrix e.injective
    have heq : (E B+s • E H).submatrix e e = B+s • H := by
      ext i j
      simp [E, reindexStar, Matrix.reindexAlgEquiv, Matrix.reindex_apply,
        Matrix.submatrix_apply]
    rwa [heq] at hh
  refine ⟨hp, ?_⟩
  have hl := reindex_log e (B+s • H) hp.isHermitian
  have hr := reindex_log e B hB.isHermitian
  have hh := hs.2
  rw [hI] at hh
  change d (E B+s • E H) (E B) = _ at hh
  unfold d at hh ⊢
  rw [← map_smul, ← map_add, ← hl, ← hr, ← map_sub, ← map_mul,
    show ∀ X, (E X).trace = X.trace from trace_reindex e] at hh
  exact hh

private def ampPositive (N : QuantumChannel a b) :
    Matrix (r × a) (r × a) ℂ →ₚ[ℂ] Matrix (r × b) (r × b) ℂ :=
  PositiveLinearMap.mk₀
    (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap))
    (fun X hX => map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (referenceAction_nonneg N (CStarMatrix.ofMatrix X)
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX)))

private lemma amp_one (N : QuantumChannel a b) :
    amp (R := r) N (1 : Matrix (r × a) (r × a) ℂ) =
      (1 : Matrix r r ℂ) ⊗ₖ act N (1 : Matrix a a ℂ) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [amp_entry]
  by_cases h : i = j
  · subst j
    have he : (fun u v => (1 : Matrix (r × a) (r × a) ℂ) (i,u) (i,v)) =
        (1 : Matrix a a ℂ) := by ext u v; simp [Matrix.one_apply]
    rw [he]
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_true, one_mul]
  · have he : (fun u v => (1 : Matrix (r × a) (r × a) ℂ) (i,u) (j,v)) =
        (0 : Matrix a a ℂ) := by ext u v; simp [Matrix.one_apply, h]
    rw [he]
    change N.toCompletelyPositiveMap 0 x y = _
    simp [Matrix.kroneckerMap_apply, Matrix.one_apply, h]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma amp_posDef (N : QuantumChannel a b)
    (hN : (act N (1 : Matrix a a ℂ)).PosDef)
    (X : Matrix (r × a) (r × a) ℂ) (hX : X.PosDef) : (amp N X).PosDef := by
  let e := Fintype.equivFin (r × a)
  let E := reindexStar e
  obtain ⟨c, hc, hfloor, _⟩ := common_floor (E X) (E X)
    (hX.submatrix e.symm.injective) (hX.submatrix e.symm.injective)
  have hf : c • (1 : Matrix (r × a) (r × a) ℂ) ≤ X := by
    have hh := OrderHomClass.mono E.symm hfloor
    simpa only [map_smul, map_one, StarAlgEquiv.symm_apply_apply] using hh
  have hp : (c • amp (R := r) N (1 : Matrix (r × a) (r × a) ℂ)).PosDef := by
    rw [amp_one]
    exact (Matrix.PosDef.one.kronecker hN).smul hc
  have hh := OrderHomClass.mono (ampPositive (r := r) N) hf
  change ampPositive N (c • (1 : Matrix (r × a) (r × a) ℂ)) ≤ amp N X at hh
  have heq : ampPositive (r := r) N (c • (1 : Matrix (r × a) (r × a) ℂ)) =
      c • amp (R := r) N (1 : Matrix (r × a) (r × a) ℂ) :=
    ((ampPositive (r := r) N).toLinearMap.restrictScalars ℝ).map_smul c 1
  rw [heq] at hh
  exact (hp.isStrictlyPositive.of_le hh).posDef

private def flagIndex : ((Fin 2 × r) × a) ≃ ((r × a) ⊕ (r × a)) where
  toFun p := if p.1.1 = 0 then Sum.inl (p.1.2,p.2) else Sum.inr (p.1.2,p.2)
  invFun := Sum.elim (fun p => ((0,p.1),p.2)) (fun p => ((1,p.1),p.2))
  left_inv p := by
    rcases p with ⟨⟨i,x⟩,y⟩
    fin_cases i <;> simp
  right_inv p := by cases p <;> simp

private def flagMatrix (X Y U W : Matrix (r × a) (r × a) ℂ) :
    Matrix ((Fin 2 × r) × a) ((Fin 2 × r) × a) ℂ :=
  reindexStar (flagIndex (r := r) (a := a)).symm (Matrix.fromBlocks X Y U W)

private lemma amp_flagMatrix (N : QuantumChannel a b)
    (X Y U W : Matrix (r × a) (r × a) ℂ) :
    amp N (flagMatrix X Y U W) =
      flagMatrix (amp N X) (amp N Y) (amp N U) (amp N W) := by
  ext ⟨⟨i,s⟩,x⟩ ⟨⟨j,t⟩,y⟩
  rw [amp_entry]
  fin_cases i <;> fin_cases j <;>
    simp [flagMatrix, reindexStar, flagIndex, Matrix.reindexAlgEquiv,
      Matrix.reindex_apply, Matrix.submatrix_apply, amp_entry]

private lemma flag_ptr_zero (V : Matrix (r × a) (r × a) ℂ)
    (hV : partialTraceRight V = 0) :
    partialTraceRight (flagMatrix 0 V Vᴴ 0) = 0 := by
  have hVs (i j : r) : ∑ x : a, V (i,x) (j,x) = 0 :=
    congrFun (congrFun hV i) j
  have hVt (i j : r) : ∑ x : a, (starRingEnd ℂ) (V (i,x) (j,x)) = 0 := by
    rw [← map_sum, hVs, map_zero]
  ext ⟨i,s⟩ ⟨j,t⟩
  fin_cases i <;> fin_cases j <;>
    simp [partialTraceRight, flagMatrix, reindexStar, flagIndex,
      Matrix.reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, hVs, hVt]

private lemma flag_offdiag_hermitian (V : Matrix (r × a) (r × a) ℂ) :
    (flagMatrix 0 V Vᴴ 0).IsHermitian := by
  exact (Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl
    Matrix.isHermitian_zero).submatrix _

private lemma amp_flag_offdiag (N : QuantumChannel a b)
    (V : Matrix (r × a) (r × a) ℂ) :
    amp N (flagMatrix 0 V Vᴴ 0) = flagMatrix 0 (amp N V) (amp N V)ᴴ 0 := by
  have hh : (amp N (flagMatrix 0 V Vᴴ 0)).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr
      ((flag_offdiag_hermitian V).isSelfAdjoint.map' (ampPositive N))
  have hz : amp (R := r) N (0 : Matrix (r × a) (r × a) ℂ) = 0 :=
    map_zero (ampPositive N)
  rw [amp_flagMatrix, hz] at hh ⊢
  have hc : amp N Vᴴ = (amp N V)ᴴ := by
    ext ⟨s,x⟩ ⟨t,y⟩
    have he := congrFun (congrFun hh.eq ((0,t),y)) ((1,s),x)
    simpa [flagMatrix, reindexStar, flagIndex, Matrix.reindexAlgEquiv,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply] using congrArg star he
  rw [hc]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma normalized_d (A B : Matrix a a ℂ) (hA : A.PosDef) (hB : B.PosDef)
    (c : ℝ) (hc : 0 < c) : d (c • A) (c • B) = c * d A B := by
  unfold d
  rw [CFC.log_smul' A hc hA.isStrictlyPositive,
    CFC.log_smul' B hc hB.isStrictlyPositive]
  simp only [add_sub_add_left_eq_sub, Matrix.smul_mul, Matrix.trace_smul,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma d_reindex (e : a ≃ b) (A B : Matrix a a ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    d (reindexStar e A) (reindexStar e B) = d A B := by
  unfold d
  rw [← reindex_log e A hA, ← reindex_log e B hB,
    ← map_sub, ← map_mul, show ∀ X, (reindexStar e X).trace = X.trace from trace_reindex e]

private def ampReal (N : QuantumChannel a b) :
    Matrix (r × a) (r × a) ℂ →ₗ[ℝ] Matrix (r × b) (r × b) ℂ :=
  (ampPositive N).toLinearMap.restrictScalars ℝ

private lemma amp_trace (N : QuantumChannel a b) (X : Matrix (r × a) (r × a) ℂ) :
    (amp N X).trace = X.trace := referenceAction_trace N (CStarMatrix.ofMatrix X)

private def cornerB (Z C : Matrix a a ℂ) (δ : ℝ) : Matrix (a ⊕ a) (a ⊕ a) ℂ :=
  Matrix.fromBlocks Z 0 0 (δ • C)

private def cornerH (V : Matrix a a ℂ) : Matrix (a ⊕ a) (a ⊕ a) ℂ :=
  Matrix.fromBlocks 0 V Vᴴ 0

private lemma cornerH_hermitian (V : Matrix a a ℂ) : (cornerH V).IsHermitian :=
  Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero rfl Matrix.isHermitian_zero

private lemma cornerH_trace (V : Matrix a a ℂ) : (cornerH V).trace = 0 := by
  simp [cornerH, Matrix.trace, Fintype.sum_sum_type]

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private def k (Z C V : Matrix a a ℂ) (δ : ℝ) : ℝ :=
  (cornerH V * logDeriv (cornerB Z C δ) (cornerH V)).trace.re

private def normalizedState (X : Matrix a a ℂ) (hX : X.PosDef)
    (τ : ℝ) (hτ : 0 < τ) (ht : X.trace = (τ : ℂ)) : DensityState a :=
  ⟨CStarMatrix.ofMatrix (τ⁻¹ • X),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hX.smul (inv_pos.mpr hτ)).posSemidef.nonneg,
    by
      change (τ⁻¹ • X).trace = 1
      rw [Matrix.trace_smul, ht, Complex.real_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hτ.ne', Complex.ofReal_one]⟩

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
private lemma finite_branch_matrix (rho sigma : DensityState a)
    (hR : (CStarMatrix.ofMatrix.symm rho.1).IsHermitian)
    (hS : (CStarMatrix.ofMatrix.symm sigma.1).IsHermitian) :
    finiteTraceLogRelativeEntropy rho sigma =
      d (CStarMatrix.ofMatrix.symm rho.1) (CStarMatrix.ofMatrix.symm sigma.1) := by
  let R := CStarMatrix.ofMatrix.symm rho.1
  let S := CStarMatrix.ofMatrix.symm sigma.1
  have hr : CStarMatrix.ofMatrix (CFC.log R) = CFC.log rho.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log R
      (R.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hR hR
  have hs : CStarMatrix.ofMatrix (CFC.log S) = CFC.log sigma.1 :=
    StarAlgHomClass.map_cfc CStarMatrix.ofMatrixStarAlgEquiv Real.log S
      (S.finite_real_spectrum.continuousOn _) CStarMatrix.ofMatrixL.continuous hS hS
  unfold finiteTraceLogRelativeEntropy
  rw [← hr, ← hs]
  rfl

private lemma full_support (rho sigma : DensityState a)
    (hS : (CStarMatrix.ofMatrix.symm sigma.1).PosDef) : SupportContained rho sigma := by
  intro v hv
  change (CStarMatrix.ofMatrix.symm sigma.1) *ᵥ v = 0 at hv
  have hz : v = 0 := hS.mulVec_injective (hv.trans (Matrix.mulVec_zero _).symm)
  subst v
  exact Matrix.mulVec_zero _

set_option maxHeartbeats 1000000 in
attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- With faithful channel output on the identity, actual faithful density pairs
with an explicit reference flag approximate the inverse-weighted quadratic ratio.
The input divergence is finite and strictly positive; the output coefficient may
vanish. The two limits are selected in order, first the flag weight and then the
perturbation at that fixed weight. -/
theorem faithful_density_pair_ratio_approx
    (N : QuantumChannel a b) (hN : (act N (1 : Matrix a a ℂ)).PosDef)
    (Z V : Matrix (r × a) (r × a) ℂ) (hZ : Z.PosDef)
    (hV : partialTraceRight V = 0)
    (hqin : 0 < (Vᴴ * Z⁻¹ * V).trace.re) (η : ℝ) (hη : 0 < η) :
    ∃ rho sigma : DensityState ((Fin 2 × r) × a),
      (CStarMatrix.ofMatrix.symm rho.1).PosDef ∧
      (CStarMatrix.ofMatrix.symm sigma.1).PosDef ∧
      (CStarMatrix.ofMatrix.symm (referenceState N rho).1).PosDef ∧
      (CStarMatrix.ofMatrix.symm (referenceState N sigma).1).PosDef ∧
      marginalRight rho = marginalRight sigma ∧
      marginalRight (referenceState N rho) = marginalRight (referenceState N sigma) ∧
      SupportContained rho sigma ∧
      SupportContained (referenceState N rho) (referenceState N sigma) ∧
      0 < finiteTraceLogRelativeEntropy rho sigma ∧
      |finiteTraceLogRelativeEntropy (referenceState N rho) (referenceState N sigma) /
          finiteTraceLogRelativeEntropy rho sigma -
        ( (amp N V)ᴴ * (amp N Z)⁻¹ * amp N V).trace.re /
          (Vᴴ * Z⁻¹ * V).trace.re| < η ∧
      finiteTraceLogRelativeEntropy (referenceState N rho) (referenceState N sigma) -
          finiteTraceLogRelativeEntropy (marginalRight (referenceState N rho))
            (marginalRight (referenceState N sigma)) =
        finiteTraceLogRelativeEntropy (referenceState N rho) (referenceState N sigma) := by
  classical
  have hne : Nonempty (r × a) := by
    by_contra hn
    letI : IsEmpty (r × a) := not_nonempty_iff.mp hn
    simpa only [Matrix.trace_eq_zero_of_isEmpty, Complex.zero_re, lt_self_iff_false] using hqin
  letI : Nonempty (r × a) := hne
  let Zi := Z
  let Ci : Matrix (r × a) (r × a) ℂ := 1
  let Vi := V
  let Zo := amp N Z
  let Co := amp (R := r) N (1 : Matrix (r × a) (r × a) ℂ)
  let Vo := amp N V
  have hZo : Zo.PosDef := amp_posDef N hN Z hZ
  have hCo : Co.PosDef := by
    dsimp [Co]
    rw [amp_one]
    exact Matrix.PosDef.one.kronecker hN
  let qi := (Vᴴ * Z⁻¹ * V).trace.re
  let qo := (Voᴴ * Zo⁻¹ * Vo).trace.re
  let L : ℝ → ℝ := fun δ => 2*Real.log (1/δ)
  have hlimi : Tendsto (fun δ => k Zi Ci Vi δ / L δ) (𝓝[>] 0) (𝓝 qi) := by
    have hh := rare_flag_logDeriv_limit Z Ci V hZ Matrix.PosDef.one
    simpa only [k, cornerB, cornerH, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose] using hh
  have hlimo : Tendsto (fun δ => k Zo Co Vo δ / L δ) (𝓝[>] 0) (𝓝 qo) := by
    have hh := rare_flag_logDeriv_limit Zo Co Vo hZo hCo
    simpa only [k, cornerB, cornerH, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose] using hh
  have hrat := hlimo.div hlimi hqin.ne'
  have hchoose : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      0 < δ ∧ δ < 1 ∧ qi/2 < k Zi Ci Vi δ / L δ ∧
        |(k Zo Co Vo δ / L δ) / (k Zi Ci Vi δ / L δ) - qo/qi| < η/2 := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < 1 from
        (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds),
      hlimi.eventually (Ioi_mem_nhds (show qi/2 < qi by dsimp [qi]; linarith)),
      hrat.eventually (Metric.ball_mem_nhds (qo/qi) (show 0 < η/2 by positivity))]
      with δ hδ hδ1 hki herr
    exact ⟨hδ, hδ1, hki, by simpa only [Metric.mem_ball, Real.dist_eq, Pi.div_apply] using herr⟩
  obtain ⟨δ, hδ, hδ1, hkδ, herrδ⟩ := hchoose.exists
  have hL : 0 < L δ := by
    dsimp [L]
    have hh : 1 < (1:ℝ)/δ := (lt_div_iff₀ hδ).mpr (by linarith)
    exact mul_pos (by norm_num) (Real.log_pos hh)
  have hki : 0 < k Zi Ci Vi δ :=
    (div_pos_iff_of_pos_right hL).mp (lt_trans (half_pos hqin) hkδ)
  have herrδ' : |k Zo Co Vo δ / k Zi Ci Vi δ - qo/qi| < η/2 := by
    have heq : (k Zo Co Vo δ / L δ) / (k Zi Ci Vi δ / L δ) =
        k Zo Co Vo δ / k Zi Ci Vi δ := by field_simp
    rwa [heq] at herrδ
  let Bi := cornerB Zi Ci δ
  let Hi := cornerH Vi
  let Bo := cornerB Zo Co δ
  let Ho := cornerH Vo
  have hBi : Bi.PosDef := block_diag_posDef Zi Ci hZ Matrix.PosDef.one hδ
  have hBo : Bo.PosDef := block_diag_posDef Zo Co hZo hCo hδ
  have hlocali := local_data Bi Hi hBi (cornerH_hermitian Vi) (cornerH_trace Vi)
  have hlocalo := local_data Bo Ho hBo (cornerH_hermitian Vo) (cornerH_trace Vo)
  have hQrat : Tendsto (fun e => localIntegral Bo Ho e / localIntegral Bi Hi e)
      (𝓝 0) (𝓝 (k Zo Co Vo δ / k Zi Ci Vi δ)) := by
    convert hlocalo.1.div hlocali.1 (half_pos hki).ne' using 1 <;>
      dsimp only [k, Bi, Hi, Bo, Ho] <;> field_simp
  have hchooseE : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < e ∧ (Bi+e • Hi).PosDef ∧ (Bo+e • Ho).PosDef ∧
      d (Bi+e • Hi) Bi = e^2 * localIntegral Bi Hi e ∧
      d (Bo+e • Ho) Bo = e^2 * localIntegral Bo Ho e ∧
      0 < localIntegral Bi Hi e ∧
      |localIntegral Bo Ho e / localIntegral Bi Hi e - k Zo Co Vo δ / k Zi Ci Vi δ| < η/2 := by
    filter_upwards [self_mem_nhdsWithin,
      hlocali.2.filter_mono nhdsWithin_le_nhds,
      hlocalo.2.filter_mono nhdsWithin_le_nhds,
      (hlocali.1.eventually (Ioi_mem_nhds (half_pos hki))).filter_mono nhdsWithin_le_nhds,
      (hQrat.eventually (Metric.ball_mem_nhds _ (show 0 < η/2 by positivity))).filter_mono
        nhdsWithin_le_nhds] with e he hi ho hpos herr
    exact ⟨he, hi.1, ho.1, hi.2, ho.2, hpos,
      by simpa only [Metric.mem_ball, Real.dist_eq, Pi.div_apply] using herr⟩
  obtain ⟨e, he, hAi, hAo, hdi, hdo, hIi, herrE⟩ := hchooseE.exists
  let Ei := reindexStar (flagIndex (r := r) (a := a)).symm
  let Eo := reindexStar (flagIndex (r := r) (a := b)).symm
  let Ai := Bi+e • Hi
  let Ao := Bo+e • Ho
  have hEiBi : (Ei Bi).PosDef := hBi.submatrix (flagIndex (r := r) (a := a)).injective
  have hEiAi : (Ei Ai).PosDef := hAi.submatrix (flagIndex (r := r) (a := a)).injective
  have hEoBo : (Eo Bo).PosDef := hBo.submatrix (flagIndex (r := r) (a := b)).injective
  have hEoAo : (Eo Ao).PosDef := hAo.submatrix (flagIndex (r := r) (a := b)).injective
  have hmapB : amp N (Ei Bi) = Eo Bo := by
    change amp N (flagMatrix Zi 0 0 (δ • Ci)) = flagMatrix Zo 0 0 (δ • Co)
    rw [amp_flagMatrix]
    have hz : amp (R := r) N (0 : Matrix (r × a) (r × a) ℂ) = 0 := map_zero (ampPositive N)
    have hs : amp N (δ • Ci) = δ • Co := (ampReal N).map_smul δ Ci
    rw [hz, hs]
  have hmapH : amp N (Ei Hi) = Eo Ho := amp_flag_offdiag N V
  have hmapA : amp N (Ei Ai) = Eo Ao := by
    change ampReal N (Ei (Bi+e • Hi)) = Eo (Bo+e • Ho)
    rw [map_add, map_smul, map_add, map_smul]
    change amp N (Ei Bi) + e • amp N (Ei Hi) = Eo Bo+e • Eo Ho
    rw [hmapB, hmapH]
  let τ := Bi.trace.re
  have hτ : 0 < τ := (Complex.pos_iff.mp hBi.trace_pos).1
  have hBtr : (Ei Bi).trace = (τ : ℂ) := by
    change (Bi.reindex (flagIndex (r := r) (a := a)).symm
      (flagIndex (r := r) (a := a)).symm).trace = _
    rw [trace_reindex]
    exact (D5.S3.Quantum.Foundation.FiniteTraceDistance.re_trace_eq_trace hBi.isHermitian).symm
  have hAtr : (Ei Ai).trace = (τ : ℂ) := by
    change (Ai.reindex (flagIndex (r := r) (a := a)).symm
      (flagIndex (r := r) (a := a)).symm).trace = _
    rw [trace_reindex]
    change (Bi+e • Hi).trace = _
    rw [Matrix.trace_add, Matrix.trace_smul, cornerH_trace, smul_zero, add_zero]
    exact (D5.S3.Quantum.Foundation.FiniteTraceDistance.re_trace_eq_trace hBi.isHermitian).symm
  have hBotr : (Eo Bo).trace = (τ : ℂ) := by
    rw [← hmapB, amp_trace, hBtr]
  have hAotr : (Eo Ao).trace = (τ : ℂ) := by
    rw [← hmapA, amp_trace, hAtr]
  let rho := normalizedState (Ei Ai) hEiAi τ hτ hAtr
  let sigma := normalizedState (Ei Bi) hEiBi τ hτ hBtr
  let rhoO := normalizedState (Eo Ao) hEoAo τ hτ hAotr
  let sigmaO := normalizedState (Eo Bo) hEoBo τ hτ hBotr
  have hrhoO : referenceState N rho = rhoO := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix (amp N (τ⁻¹ • Ei Ai)) = CStarMatrix.ofMatrix (τ⁻¹ • Eo Ao)
    have hs := (ampReal N).map_smul τ⁻¹ (Ei Ai)
    change amp N (τ⁻¹ • Ei Ai) = τ⁻¹ • amp N (Ei Ai) at hs
    rw [hs, hmapA]
  have hsigmaO : referenceState N sigma = sigmaO := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix (amp N (τ⁻¹ • Ei Bi)) = CStarMatrix.ofMatrix (τ⁻¹ • Eo Bo)
    have hs := (ampReal N).map_smul τ⁻¹ (Ei Bi)
    change amp N (τ⁻¹ • Ei Bi) = τ⁻¹ • amp N (Ei Bi) at hs
    rw [hs, hmapB]
  have hpR : (CStarMatrix.ofMatrix.symm rho.1).PosDef := hEiAi.smul (inv_pos.mpr hτ)
  have hpS : (CStarMatrix.ofMatrix.symm sigma.1).PosDef := hEiBi.smul (inv_pos.mpr hτ)
  have hpRO : (CStarMatrix.ofMatrix.symm rhoO.1).PosDef := hEoAo.smul (inv_pos.mpr hτ)
  have hpSO : (CStarMatrix.ofMatrix.symm sigmaO.1).PosDef := hEoBo.smul (inv_pos.mpr hτ)
  have hD : finiteTraceLogRelativeEntropy rho sigma = τ⁻¹ * e^2 * localIntegral Bi Hi e := by
    rw [finite_branch_matrix _ _ hpR.isHermitian hpS.isHermitian]
    change d (τ⁻¹ • Ei Ai) (τ⁻¹ • Ei Bi) = _
    rw [normalized_d _ _ hEiAi hEiBi _ (inv_pos.mpr hτ),
      d_reindex _ _ _ hAi.isHermitian hBi.isHermitian, hdi]
    ring
  have hDO : finiteTraceLogRelativeEntropy rhoO sigmaO = τ⁻¹ * e^2 * localIntegral Bo Ho e := by
    rw [finite_branch_matrix _ _ hpRO.isHermitian hpSO.isHermitian]
    change d (τ⁻¹ • Eo Ao) (τ⁻¹ • Eo Bo) = _
    rw [normalized_d _ _ hEoAo hEoBo _ (inv_pos.mpr hτ),
      d_reindex _ _ _ hAo.isHermitian hBo.isHermitian, hdo]
    ring
  have hpositive : 0 < finiteTraceLogRelativeEntropy rho sigma := by
    rw [hD]
    exact mul_pos (mul_pos (inv_pos.mpr hτ) (sq_pos_of_pos he)) hIi
  have hquot : finiteTraceLogRelativeEntropy rhoO sigmaO /
      finiteTraceLogRelativeEntropy rho sigma = localIntegral Bo Ho e / localIntegral Bi Hi e := by
    rw [hD, hDO]
    field_simp
  have hmarg : marginalRight rho = marginalRight sigma := by
    apply Subtype.ext
    change CStarMatrix.ofMatrix (partialTraceRight (τ⁻¹ • Ei Ai)) =
      CStarMatrix.ofMatrix (partialTraceRight (τ⁻¹ • Ei Bi))
    rw [partialTraceRight_smul, partialTraceRight_smul]
    congr 2
    change partialTraceRight (Ei (Bi+e • Hi)) = partialTraceRight (Ei Bi)
    rw [map_add, map_smul, partialTraceRight_add, partialTraceRight_smul]
    change partialTraceRight (Ei Bi) + e • partialTraceRight (flagMatrix 0 V Vᴴ 0) = _
    rw [flag_ptr_zero V hV, smul_zero, add_zero]
  have hmargO : marginalRight (referenceState N rho) = marginalRight (referenceState N sigma) := by
    apply Subtype.ext
    have hh := congrArg Subtype.val hmarg
    change CStarMatrix.ofMatrix (partialTraceRight (amp N (τ⁻¹ • Ei Ai))) =
      CStarMatrix.ofMatrix (partialTraceRight (amp N (τ⁻¹ • Ei Bi)))
    have hp : partialTraceRight (amp N (τ⁻¹ • Ei Ai)) = partialTraceRight (τ⁻¹ • Ei Ai) :=
      ptr_amp N (τ⁻¹ • Ei Ai)
    have hq : partialTraceRight (amp N (τ⁻¹ • Ei Bi)) = partialTraceRight (τ⁻¹ • Ei Bi) :=
      ptr_amp N (τ⁻¹ • Ei Bi)
    rw [hp, hq]
    exact hh
  refine ⟨rho, sigma, hpR, hpS, by rwa [hrhoO], by rwa [hsigmaO], hmarg, hmargO,
    full_support rho sigma hpS, ?_, hpositive, ?_, ?_⟩
  · rw [hrhoO, hsigmaO]
    exact full_support rhoO sigmaO hpSO
  · rw [hrhoO, hsigmaO, hquot]
    calc
      _ = |(localIntegral Bo Ho e / localIntegral Bi Hi e - k Zo Co Vo δ / k Zi Ci Vi δ) +
          (k Zo Co Vo δ / k Zi Ci Vi δ - qo/qi)| := by congr 1; ring
      _ ≤ |localIntegral Bo Ho e / localIntegral Bi Hi e - k Zo Co Vo δ / k Zi Ci Vi δ| +
          |k Zo Co Vo δ / k Zi Ci Vi δ - qo/qi| := abs_add_le _ _
      _ < η := by linarith
  · rw [hmargO, finiteTraceLogRelativeEntropy_self, sub_zero]

end D5.S3.Quantum.Divergence.UmegakiFaithfulLowerRatio
