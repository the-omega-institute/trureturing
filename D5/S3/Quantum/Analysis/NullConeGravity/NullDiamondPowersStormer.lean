/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondPowersStormer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Powers–Størmer inequality and trace-class stability of covariance roots. -/

import D5.S3.Quantum.Analysis.TraceClass.IdealNorm
import D5.S3.Quantum.Analysis.TraceClass.Compact
import D5.S3.Quantum.Analysis.TraceClass.Spectral
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondConverseLowerBound

/-! The operator-norm closed compact ideal controls the square-root difference.
The diagonal estimate in its real eigenbasis then controls the Hilbert–Schmidt sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology Polynomial CFC
open ContinuousLinearMap HilbertSchmidt
open D5.S3.Quantum.Analysis.CompactEigenbasis
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt

namespace D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondPowersStormer

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local notation "Op" => H →L[ℂ] H

omit [CompleteSpace H] in
private theorem compact_mul_left {D : Op} (h : IsCompactOperator D) (T : Op) :
    IsCompactOperator (T * D : Op) :=
  h.clm_comp T

omit [CompleteSpace H] in
private theorem compact_mul_right {D : Op} (h : IsCompactOperator D) (T : Op) :
    IsCompactOperator (D * T : Op) :=
  h.comp_clm T

omit [CompleteSpace H] in
private theorem compact_poly_sub {A B : Op} (h : IsCompactOperator (B - A))
    (p : ℝ[X]) : IsCompactOperator (Polynomial.aeval B p - Polynomial.aeval A p : Op) := by
  have hp (n : ℕ) : IsCompactOperator (B ^ n - A ^ n : Op) := by
    induction n with
    | zero => simpa using (isCompactOperator_zero : IsCompactOperator (0 : Op))
    | succ n ih =>
      rw [show B ^ (n + 1) - A ^ (n + 1) =
          B * (B ^ n - A ^ n) + (B - A) * A ^ n by
        rw [pow_succ', pow_succ']; noncomm_ring]
      exact (compact_mul_left ih B).add (compact_mul_right h (A ^ n))
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact hp.add hq
  | monomial n r =>
    simpa only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, ← smul_sub, FunLike.coe_smul] using (hp n).smul r

set_option maxHeartbeats 1000000 in
-- Elaborate the real functional calculus on the bounded operator algebra.
/-- Compact perturbations of positive bounded operators give compact root differences. -/
theorem isCompactOperator_sqrt_sub_of_isCompactOperator_sub
    {A B : Op} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : IsCompactOperator (B - A)) :
    IsCompactOperator (CFC.sqrt B - CFC.sqrt A) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · rw [Subsingleton.elim (CFC.sqrt B - CFC.sqrt A) (0 : Op)]
    exact isCompactOperator_zero
  let R := max ‖A‖ ‖B‖
  have hclosed : IsClosed {D : Op | IsCompactOperator D} :=
    isClosed_setOfPred_isCompactOperator
  change CFC.sqrt B - CFC.sqrt A ∈ {D : Op | IsCompactOperator D}
  rw [← hclosed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 R Real.sqrt
    Real.continuous_sqrt.continuousOn (ε / 3) (by positivity)
  have happrox (X : Op) (hx : 0 ≤ X) (hnorm : ‖X‖ ≤ R) :
      ‖Polynomial.aeval X q - CFC.sqrt X‖ ≤ ε / 3 := by
    rw [CFC.sqrt_eq_real_sqrt X hx, cfcₙ_eq_cfc Real.continuous_sqrt.continuousOn Real.sqrt_zero,
      ← cfc_polynomial q X (IsSelfAdjoint.of_nonneg hx), ← cfc_sub q.eval Real.sqrt X]
    apply norm_cfc_le (by positivity)
    intro t ht
    have ht₀ := spectrum_nonneg_of_nonneg hx ht
    have htR := (spectrum.norm_le_norm_of_mem ht).trans hnorm
    exact (hq t ⟨ht₀, by simpa [Real.norm_eq_abs, abs_of_nonneg ht₀] using htR⟩).le
  refine ⟨Polynomial.aeval B q - Polynomial.aeval A q, compact_poly_sub h q, ?_⟩
  have ha := happrox A hA (le_max_left _ _)
  have hb := happrox B hB (le_max_right _ _)
  rw [dist_comm, dist_eq_norm, sub_sub_sub_comm]
  linarith [norm_sub_le (Polynomial.aeval B q - CFC.sqrt B) (Polynomial.aeval A q - CFC.sqrt A)]

private theorem root_mul_sub (A B : Op) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    B - A = CFC.sqrt B * (CFC.sqrt B - CFC.sqrt A) +
      (CFC.sqrt B - CFC.sqrt A) * CFC.sqrt A := by
  rw [mul_sub, sub_mul, CFC.sqrt_mul_sqrt_self _ hA, CFC.sqrt_mul_sqrt_self _ hB]
  abel

private theorem diagonal_root_sq_le {A B : Op} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (e : H) (he : ‖e‖ = 1) (l : ℝ)
    (hl : (CFC.sqrt B - CFC.sqrt A) e = (l : ℂ) • e) :
    ‖(CFC.sqrt B - CFC.sqrt A) e‖ ^ 2 ≤ ‖⟪e, (B - A) e⟫_ℂ‖ := by
  let D := CFC.sqrt B - CFC.sqrt A
  let a := (⟪e, CFC.sqrt A e⟫_ℂ).re
  let b := (⟪e, CFC.sqrt B e⟫_ℂ).re
  have hD : D.adjoint = D := isSelfAdjoint_iff'.mp
    ((IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).sub
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)))
  have ha : 0 ≤ a := (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)).re_inner_nonneg_right e
  have hb : 0 ≤ b := (nonneg_iff_isPositive.mp (CFC.sqrt_nonneg B)).re_inner_nonneg_right e
  have he' : ⟪e, e⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, he]
  have hd : b - a = l := by
    have h := congrArg (fun x => (⟪e, x⟫_ℂ).re) hl
    simpa only [sub_apply, inner_sub_right, inner_smul_right, he', mul_one,
      Complex.sub_re, Complex.ofReal_re] using h
  have hdiag : (⟪e, (B - A) e⟫_ℂ).re = l * (b + a) := by
    rw [root_mul_sub A B hA hB]
    change (⟪e, (CFC.sqrt B * D + D * CFC.sqrt A) e⟫_ℂ).re = _
    simp only [add_apply, mul_apply_eq_comp, inner_add_right, ← adjoint_inner_left D,
      hD, show D e = (l : ℂ) • e from hl, map_smul, inner_smul_right, inner_smul_left,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_ofReal, zero_mul, sub_zero]
    change l * b + l * a = _
    ring
  have habs : |l| ≤ b + a := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [hl, norm_smul, he, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc
    |l| ^ 2 ≤ |l| * (b + a) := by rw [pow_two]; gcongr
    _ = |(⟪e, (B - A) e⟫_ℂ).re| := by rw [hdiag, abs_mul, abs_of_nonneg (add_nonneg hb ha)]
    _ ≤ ‖⟪e, (B - A) e⟫_ℂ‖ := Complex.abs_re_le_norm _

private theorem powers_stormer_estimate {A B : Op} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : IsTraceClass (B - A)) :
    ∃ hD : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A), hsSq _ hD ≤ traceNorm _ h := by
  have hsa : IsSelfAdjoint (CFC.sqrt B - CFC.sqrt A) :=
    (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg B)).sub
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A))
  obtain ⟨w, b, l, hl⟩ := exists_setIndex_real_eigenbasis_rclike
    (isCompactOperator_sqrt_sub_of_isCompactOperator_sub hA hB (isCompactOperator_of_isTraceClass h))
    (isSelfAdjoint_iff_isSymmetric.mp hsa)
  have hbound (i : w) := diagonal_root_sq_le hA hB (b i) (b.orthonormal.norm_eq_one i) (l i) (hl i)
  have h₁ : ‖(1 : Op)‖ ≤ 1 := opNorm_le_bound _ zero_le_one (by simp)
  have hsum : Summable (fun i : w => ‖⟪b i, (B - A) (b i)⟫_ℂ‖) := by
    simpa only [one_apply_eq_self] using summable_norm_inner_contraction_of_isTraceClass h h₁ b
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hbound hsum
  refine ⟨⟨w, b, hs⟩, ?_⟩
  unfold hsSq
  rw [(hasSum_norm_sq_apply_of_basis b (exists_hilbertBasis ℂ H).choose_spec.choose hs).tsum_eq]
  refine (hs.tsum_le_tsum hbound hsum).trans ?_
  simpa only [one_apply_eq_self] using tsum_norm_inner_contraction_le_traceNorm h h₁ b

/-- The root difference of a trace-class perturbation is Hilbert–Schmidt. -/
theorem powers_stormer_isHilbertSchmidt {A B : Op} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : IsTraceClass (B - A)) : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A) :=
  (powers_stormer_estimate hA hB h).choose

/-- The sharp squared Hilbert–Schmidt bound on an arbitrary complex Hilbert space. -/
theorem powers_stormer_hsSq_le {A B : Op} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : IsTraceClass (B - A)) :
    hsSq _ (powers_stormer_isHilbertSchmidt hA hB h) ≤ traceNorm _ h :=
  (powers_stormer_estimate hA hB h).choose_spec


/-- The identity and zero on the complex line attain equality. -/
theorem powers_stormer_sharp :
    ∃ h : IsTraceClass ((1 : ℂ →L[ℂ] ℂ) - 0),
      hsSq _ (powers_stormer_isHilbertSchmidt le_rfl zero_le_one h) = 1 ∧
        traceNorm _ h = 1 := by
  let h := isTraceClass_of_finiteDimensional ((1 : ℂ →L[ℂ] ℂ) - 0)
  refine ⟨h, ?_, ?_⟩
  · obtain ⟨h₁, h₀, hf, hW, hΔ, hsq, _⟩ := quarterPower_sqrt_sharp
    simp only [CFC.sqrt_zero, CFC.sqrt_one, zero_sub, sub_zero, hsSq, neg_apply, norm_neg] at hsq ⊢
    exact hsq
  · obtain ⟨h₁, h₀, hf, hW, hΔ, hsq, _⟩ := quarterPower_sqrt_sharp
    rw [← tsum_sqrt_abs_norm_sq_eq_traceNorm h (exists_hilbertBasis ℂ ℂ).choose_spec.choose]
    simp only [sub_zero, CFC.abs_of_nonneg _ zero_le_one, CFC.sqrt_one]
    simpa only [CFC.sqrt_zero, CFC.sqrt_one, zero_sub, hsSq, neg_apply, norm_neg] using hsq

private theorem congr_nonneg (C : K →L[ℂ] H) {A : Op} (h : 0 ≤ A) :
    0 ≤ adjointCongr C A :=
  nonneg_iff_isPositive.mpr ((nonneg_iff_isPositive.mp h).adjoint_conj C)

private theorem congr_sub (C : K →L[ℂ] H) (A B : Op) :
    adjointCongr C (B - A) = adjointCongr C B - adjointCongr C A := by
  ext x
  simp [adjointCongr]

private theorem positive_trace_congr (C : K →L[ℂ] H) {X : Op}
    (hx : 0 ≤ X) (ht : IsTraceClass X) :
    ∃ hc : IsTraceClass (adjointCongr C X),
      traceNorm _ hc ≤ ‖C‖ ^ 2 * traceNorm _ ht := by
  let S := CFC.sqrt X
  obtain ⟨u, b, _⟩ := exists_hilbertBasis ℂ K
  obtain ⟨v, d, _⟩ := exists_hilbertBasis ℂ H
  have hS : IsHilbertSchmidt S := by
    simpa only [S, CFC.abs_of_nonneg X hx] using isHilbertSchmidt_sqrt_abs_of_isTraceClass ht
  have hSa : S.adjoint = S := isSelfAdjoint_iff'.mp (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg X))
  let f (j : v) (i : u) := ‖⟪b i, C.adjoint (S (d j))⟫_ℂ‖ ^ 2
  have hrow (j : v) : HasSum (f j) (‖C.adjoint (S (d j))‖ ^ 2) :=
    hasSum_norm_sq_inner_basis b _
  have hcol (i : u) : HasSum (fun j => f j i) (‖S (C (b i))‖ ^ 2) := by
    apply (hasSum_norm_sq_inner_basis d (S (C (b i)))).congr_fun
    intro j
    dsimp only [f]
    have hc := adjoint_inner_left S (C (b i)) (d j)
    rw [hSa] at hc
    rw [adjoint_inner_right, ← hc, ← inner_conj_symm (S (d j)) (C (b i)),
      RCLike.norm_conj]
  have hSsum := summable_norm_sq_apply_of_hilbertBasis v d hS
  have hle (j : v) : ‖C.adjoint (S (d j))‖ ^ 2 ≤ ‖C‖ ^ 2 * ‖S (d j)‖ ^ 2 := by
    rw [← mul_pow, ← adjoint.norm_map C]
    exact pow_le_pow_left₀ (norm_nonneg _) (C.adjoint.le_opNorm _) 2
  have hsum := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle (hSsum.mul_left _)
  have hf : Summable (Function.uncurry f) := (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun j => (hrow j).summable, hsum.congr (fun j => (hrow j).tsum_eq.symm)⟩
  have hflip : Summable (Function.uncurry (fun i j => f j i)) :=
    (Equiv.prodComm u v).summable_iff.mpr hf
  have hcols := ((summable_prod_of_nonneg (fun _ : u × v => sq_nonneg _)).mp hflip).2.congr
    (fun i => (hcol i).tsum_eq)
  have hform (i : u) :
      (⟪b i, CFC.abs (adjointCongr C X) (b i)⟫_ℂ).re = ‖S (C (b i))‖ ^ 2 := by
    rw [CFC.abs_of_nonneg _ (congr_nonneg C hx)]
    simp only [adjointCongr, comp_apply, adjoint_inner_right]
    rw [S.apply_norm_sq_eq_inner_adjoint_right, hSa]
    exact congrArg (fun T : Op => (⟪C (b i), T (C (b i))⟫_ℂ).re) (CFC.sqrt_mul_sqrt_self X hx).symm
  have hc : IsTraceClass (adjointCongr C X) := ⟨u, b, hcols.congr (fun i => (hform i).symm)⟩
  refine ⟨hc, ?_⟩
  rw [traceNorm_eq_of_hilbertBasis hc b]
  simp_rw [hform, ← fun i => (hcol i).tsum_eq]
  have hswap : (∑' i, ∑' j, f j i) = ∑' j, ∑' i, f j i := hf.tsum_comm' (fun j =>
    (hrow j).summable) (fun i => (hcol i).summable)
  rw [hswap]
  simp_rw [(hrow _).tsum_eq]
  exact (hsum.tsum_le_tsum hle (hSsum.mul_left _)).trans_eq
    (by rw [tsum_mul_left]; congr 1; simpa only [S, CFC.abs_of_nonneg X hx] using
      tsum_sqrt_abs_norm_sq_eq_traceNorm ht d)

private theorem shifted_bounds {X : Op} (hsa : IsSelfAdjoint X) (h : IsTraceClass X) :
    ∃ (hp : IsTraceClass (CFC.abs X)) (hm : IsTraceClass (CFC.abs X - X)),
      0 ≤ CFC.abs X - X ∧ traceNorm _ hp = traceNorm _ h ∧
        traceNorm _ hm ≤ 2 * traceNorm _ h := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hp : IsTraceClass (CFC.abs X) := ⟨w, b, by
    simpa only [CFC.abs_of_nonneg _ (CFC.abs_nonneg X)] using summable_inner_abs_of_hilbertBasis h b⟩
  have he := CFC.abs_sub_self X hsa
  have hmpos : 0 ≤ CFC.abs X - X := he ▸ nsmul_nonneg (CFC.negPart_nonneg X) 2
  have hle : CFC.abs X - X ≤ 2 • CFC.abs X := by
    rw [he, ← CFC.posPart_add_negPart X hsa]
    exact nsmul_le_nsmul_right (le_add_of_nonneg_left (CFC.posPart_nonneg X)) 2
  have hdiag (i : w) : (⟪b i, (CFC.abs X - X) (b i)⟫_ℂ).re ≤
      2 * (⟪b i, CFC.abs X (b i)⟫_ℂ).re := by
    have hpos := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hle)).re_inner_nonneg_right (b i)
    change 0 ≤ (⟪b i, (2 • CFC.abs X - (CFC.abs X - X)) (b i)⟫_ℂ).re at hpos
    simp only [two_nsmul, sub_apply, add_apply, inner_sub_right, inner_add_right,
      Complex.sub_re, Complex.add_re] at hpos
    simp only [sub_apply, inner_sub_right, Complex.sub_re]
    linarith
  have hsum := summable_inner_abs_of_hilbertBasis h b
  have hms : Summable (fun i : w => (⟪b i, (CFC.abs X - X) (b i)⟫_ℂ).re) := Summable.of_nonneg_of_le
    (fun i : w => (nonneg_iff_isPositive.mp hmpos).re_inner_nonneg_right (b i))
    hdiag (hsum.mul_left 2)
  have hm : IsTraceClass (CFC.abs X - X) := ⟨w, b, by
    simpa only [CFC.abs_of_nonneg _ hmpos] using hms⟩
  refine ⟨hp, hm, hmpos, ?_, ?_⟩
  · rw [traceNorm_eq_of_hilbertBasis hp b, traceNorm_eq_of_hilbertBasis h b,
      CFC.abs_of_nonneg _ (CFC.abs_nonneg X)]
  · rw [traceNorm_eq_of_hilbertBasis hm b, traceNorm_eq_of_hilbertBasis h b,
      CFC.abs_of_nonneg _ hmpos, ← tsum_mul_left]
    exact hms.tsum_le_tsum hdiag (hsum.mul_left 2)

private theorem hsSq_add_three {U V W : Op} (hu : IsHilbertSchmidt U)
    (hv : IsHilbertSchmidt V) (hw : IsHilbertSchmidt W) :
    hsSq _ (isHilbertSchmidt_add (isHilbertSchmidt_add hu hv) hw) ≤
      3 * (hsSq U hu + hsSq V hv + hsSq W hw) := by
  let b := (exists_hilbertBasis ℂ H).choose_spec.choose
  have hu' := summable_norm_sq_apply_of_hilbertBasis _ b hu
  have hv' := summable_norm_sq_apply_of_hilbertBasis _ b hv
  have hw' := summable_norm_sq_apply_of_hilbertBasis _ b hw
  unfold hsSq
  rw [← hu'.tsum_add hv', ← (hu'.add hv').tsum_add hw', ← tsum_mul_left]
  refine (summable_norm_sq_apply_of_hilbertBasis _ b
    (isHilbertSchmidt_add (isHilbertSchmidt_add hu hv) hw)).tsum_le_tsum ?_
    (((hu'.add hv').add hw').mul_left 3)
  intro i
  simp only [add_apply]
  have hn : ‖U (b i) + V (b i) + W (b i)‖ ≤ ‖U (b i)‖ + ‖V (b i)‖ + ‖W (b i)‖ :=
    (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans ?_
  nlinarith [sq_nonneg (‖U (b i)‖ - ‖V (b i)‖), sq_nonneg (‖U (b i)‖ - ‖W (b i)‖),
    sq_nonneg (‖V (b i)‖ - ‖W (b i)‖)]

set_option maxHeartbeats 2000000 in
-- Elaborate the adjoint factorization between quarter roots.
private theorem quarter_shift_congr {A E W : Op} (h : A ≤ E)
    (hW : IsHilbertSchmidt W) :
    ∃ (V : Op) (hv : IsHilbertSchmidt V), hsSq V hv ≤ hsSq W hW ∧
      quarterRoot A * W * quarterRoot A = quarterRoot E * V * quarterRoot E := by
  have hroot := CFC.sqrt_le_sqrt A E h
  have hnorm (x : H) : ‖quarterRoot A x‖ ≤ 1 * ‖quarterRoot E x‖ := by
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    have heq (T : Op) :
        ‖quarterRoot T x‖ ^ 2 = (⟪x, CFC.sqrt T x⟫_ℂ).re := by
      rw [(quarterRoot T).apply_norm_sq_eq_inner_adjoint_right,
        isSelfAdjoint_iff'.mp (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _))]
      exact congrArg (fun U : Op => (⟪x, U x⟫_ℂ).re)
        (CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg T))
    rw [heq A, heq E]
    have hp := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hroot)).re_inner_nonneg_right x
    change 0 ≤ (⟪x, (CFC.sqrt E - CFC.sqrt A) x⟫_ℂ).re at hp
    simpa only [sub_apply, inner_sub_right, Complex.sub_re, sub_nonneg] using hp
  obtain ⟨Z, hZ, hfac⟩ := exists_bounded_factor (quarterRoot A) (quarterRoot E) zero_le_one hnorm
  obtain ⟨hV, hVle⟩ := adjointCongr_hsSq_le Z hW
  refine ⟨_, hV, hVle.trans ?_, ?_⟩
  · have hn : 0 ≤ hsSq W hW := tsum_nonneg (fun _ => sq_nonneg _)
    simpa only [one_pow, one_mul] using
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hZ 4) hn
  · have hstar := congrArg adjoint hfac
    rw [adjoint_comp, isSelfAdjoint_iff'.mp (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)),
      isSelfAdjoint_iff'.mp (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _))] at hstar
    change quarterRoot A * W * quarterRoot A = quarterRoot E * (Z.adjoint * (W * Z)) * quarterRoot E
    change quarterRoot A = Z * quarterRoot E at hfac
    change quarterRoot A = quarterRoot E * Z.adjoint at hstar
    calc
      _ = (quarterRoot E * Z.adjoint) * W * (Z * quarterRoot E) :=
        congrArg₂ (fun L R : Op => L * W * R) hstar hfac
      _ = _ := by noncomm_ring

set_option maxHeartbeats 1500000 in
-- Elaborate square roots and trace-class bounds across the two spaces.
/-- An additional self-adjoint trace-class term preserves the square-root estimate after congruence. -/
theorem quarterPower_add_traceClass_congruence_sqrt_hs
    {A B W X : Op} (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : IsHilbertSchmidt W)
    (hsa : IsSelfAdjoint X) (hX : IsTraceClass X)
    (hD : B - A = quarterRoot A * W * quarterRoot A + X) (C : K →L[ℂ] H) :
    ∃ h : IsHilbertSchmidt (CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C A)),
      hsSq _ h ≤ 3 * ‖C‖ ^ 2 * (hsSq W hW + 3 * traceNorm X hX) := by
  let E := A + CFC.abs X
  let F := B + (CFC.abs X - X)
  obtain ⟨hp, hm, hmp, htp, htm⟩ := shifted_bounds hsa hX
  have hae : A ≤ E := le_add_of_nonneg_right (CFC.abs_nonneg X)
  have hE : 0 ≤ E := hA.trans hae
  have hF : 0 ≤ F := add_nonneg hB hmp
  obtain ⟨V, hv, hvle, hfactor⟩ := quarter_shift_congr hae hW
  have hFE : F - E = quarterRoot E * V * quarterRoot E := by
    calc
      F - E = B - A - X := by dsimp [F, E]; abel
      _ = _ := by rw [hD, add_sub_cancel_right, hfactor]
  obtain ⟨hv', hv'le⟩ := quarterPower_congruence_sqrt_hsSq_le hE hF hv hFE C
  obtain ⟨hp', hp'le⟩ := positive_trace_congr C (CFC.abs_nonneg X) hp
  obtain ⟨hm', hm'le⟩ := positive_trace_congr C hmp hm
  have he : adjointCongr C E - adjointCongr C A = adjointCongr C (CFC.abs X) := by
    rw [← congr_sub]; simp [E]
  have hf : adjointCongr C F - adjointCongr C B = adjointCongr C (CFC.abs X - X) := by
    rw [← congr_sub]; simp [F]
  let U := CFC.sqrt (adjointCongr C F) - CFC.sqrt (adjointCongr C B)
  let P := CFC.sqrt (adjointCongr C E) - CFC.sqrt (adjointCongr C A)
  let V' := CFC.sqrt (adjointCongr C F) - CFC.sqrt (adjointCongr C E)
  have htU : IsTraceClass (adjointCongr C F - adjointCongr C B) := hf ▸ hm'
  have htP : IsTraceClass (adjointCongr C E - adjointCongr C A) := he ▸ hp'
  have hU : IsHilbertSchmidt U := powers_stormer_isHilbertSchmidt
    (congr_nonneg C hB) (congr_nonneg C hF) htU
  have hP : IsHilbertSchmidt P := powers_stormer_isHilbertSchmidt
    (congr_nonneg C hA) (congr_nonneg C hE) htP
  have hnorm {Y Z : K →L[ℂ] K} (h : Y = Z) (hy : IsTraceClass Y) (hz : IsTraceClass Z) :
      traceNorm Y hy = traceNorm Z hz := by subst Z; rfl
  have hUle : hsSq U hU ≤ ‖C‖ ^ 2 * (2 * traceNorm X hX) := by
    refine (powers_stormer_hsSq_le (congr_nonneg C hB) (congr_nonneg C hF) htU).trans ?_
    refine (show traceNorm _ htU ≤ ‖C‖ ^ 2 * traceNorm _ hm from ?_).trans
      (mul_le_mul_of_nonneg_left htm (sq_nonneg _))
    exact (hnorm hf htU hm').le.trans hm'le
  have hPle : hsSq P hP ≤ ‖C‖ ^ 2 * traceNorm X hX := by
    refine (powers_stormer_hsSq_le (congr_nonneg C hA) (congr_nonneg C hE) htP).trans ?_
    exact (hnorm he htP hp').le.trans (hp'le.trans (mul_le_mul_of_nonneg_left htp.le (sq_nonneg _)))
  have hneg : IsHilbertSchmidt (-U) := by
    simpa using isHilbertSchmidt_smul (-1 : ℂ) hU
  have hnegEq : hsSq (-U) hneg = hsSq U hU := by simp [hsSq]
  have hadd : -U + V' + P = CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C A) := by
    dsimp [U, V', P]; abel
  have hfinal := isHilbertSchmidt_add (isHilbertSchmidt_add hneg hv') hP
  refine ⟨hadd ▸ hfinal, ?_⟩
  have hh := hsSq_add_three hneg hv' hP
  rw [hnegEq] at hh
  have hh' : hsSq _ (hadd ▸ hfinal) ≤ 3 * (hsSq U hU + hsSq V' hv' + hsSq P hP) := by
    change hsSq (-U + V' + P) hfinal ≤ _ at hh
    unfold hsSq at hh ⊢
    rw [← hadd]
    exact hh
  refine hh'.trans ?_
  have hVle := hv'le.trans (mul_le_mul_of_nonneg_left hvle (sq_nonneg ‖C‖))
  calc
    _ ≤ 3 * (‖C‖ ^ 2 * (2 * traceNorm X hX) + ‖C‖ ^ 2 * hsSq W hW +
        ‖C‖ ^ 2 * traceNorm X hX) := by gcongr
    _ = _ := by ring

/-- Smooth trace-class corrections preserve the Hilbert–Schmidt difference before congruence. -/
theorem quarterPower_add_traceClass_sqrt_hs
    {A B W X : Op} (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : IsHilbertSchmidt W)
    (hsa : IsSelfAdjoint X) (hX : IsTraceClass X)
    (hD : B - A = quarterRoot A * W * quarterRoot A + X) :
    ∃ h : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A),
      hsSq _ h ≤ 3 * (hsSq W hW + 3 * traceNorm X hX) := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · have h : IsHilbertSchmidt (CFC.sqrt B - CFC.sqrt A) := by
      rw [Subsingleton.elim (CFC.sqrt B - CFC.sqrt A) (0 : Op)]
      exact isHilbertSchmidt_zero
    refine ⟨h, ?_⟩
    simp only [hsSq, Subsingleton.elim (CFC.sqrt B - CFC.sqrt A) (0 : Op), zero_apply,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), tsum_zero]
    have hn : 0 ≤ hsSq W hW := tsum_nonneg (fun _ => sq_nonneg _)
    exact mul_nonneg (by norm_num) (add_nonneg hn (mul_nonneg (by norm_num) (traceNorm_nonneg X hX)))
  · simpa only [adjointCongr, one_def, adjoint_id, comp_id, id_comp, norm_id, one_pow, mul_one]
      using quarterPower_add_traceClass_congruence_sqrt_hs hA hB hW hsa hX hD (1 : Op)

private theorem trace_congr (C : K →L[ℂ] H) {X : Op} (hx : IsSelfAdjoint X) (h : IsTraceClass X) :
    IsTraceClass (adjointCongr C X) := by
  obtain ⟨hp, hm, hmp, _, _⟩ := shifted_bounds hx h
  obtain ⟨hp', _⟩ := positive_trace_congr C (CFC.abs_nonneg X) hp
  obtain ⟨hm', _⟩ := positive_trace_congr C hmp hm
  have hn : IsTraceClass (-adjointCongr C (CFC.abs X - X)) := by
    simpa using isTraceClass_mul_mul (A := -1) (B := 1) hm'
  have hsub : IsTraceClass (adjointCongr C (CFC.abs X) - adjointCongr C (CFC.abs X - X)) := by
    simpa only [sub_eq_add_neg] using isTraceClass_add hp' hn
  rwa [← congr_sub, sub_sub_cancel] at hsub

open _root_.NullConeGravity in
/-- The normalized converse persists when the covariance includes a trace-class correction. -/
theorem not_hs_sqrt_diff_of_add_traceClass_not_hs {A B T X : Op} {c : ℝ}
    (hc : 0 < c) (hN : c • (1 : Op) ≤ 1 + T) (hA : 0 ≤ A)
    (hAupper : A ≤ (2 : ℝ) • (1 : Op)) (hAT : 0 ≤ A + T)
    (hATupper : 0 ≤ (1 + T) - (A - 1)) (hB : 0 ≤ B)
    (hB_eq : B = A + T + X) (hX : IsTraceClass X) (hT : ¬ IsHilbertSchmidt T) :
    let C := covarianceNormalizer (1 + T)
    ¬ IsHilbertSchmidt (CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C A)) := by
  let C := covarianceNormalizer (1 + T)
  have hx : X = B - (A + T) := by rw [hB_eq, add_sub_cancel_left]
  have hsa : IsSelfAdjoint X := hx ▸ (IsSelfAdjoint.of_nonneg hB).sub (IsSelfAdjoint.of_nonneg hAT)
  have ht : IsTraceClass (adjointCongr C B - adjointCongr C (A + T)) := by
    rw [← congr_sub, ← hx]
    exact trace_congr C hsa hX
  have h := powers_stormer_isHilbertSchmidt (congr_nonneg C hAT) (congr_nonneg C hB) ht
  change ¬ IsHilbertSchmidt (CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C A))
  intro hd
  apply not_hs_sqrt_diff_of_not_hs_T hc hN hA hAupper hAT hATupper hT
  have he : covarianceRootDiff (1 + T) A T =
      (CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C A)) -
        (CFC.sqrt (adjointCongr C B) - CFC.sqrt (adjointCongr C (A + T))) := by
    unfold covarianceRootDiff
    abel
  exact he.symm ▸ isHilbertSchmidt_sub hd h

end D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondPowersStormer
