/- GID: D5/S3/Weil/TestFunctions/FiniteMomentElimination
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/FiniteMomentElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Endpoint delta jets remove moments while leaving Weil tests unchanged. -/

import D5.S3.Weil.ZetaCore.ExplicitFormula
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.VectorMeasure.Integral

namespace D5.S3.Weil.TestFunctions.FiniteMomentElimination

open Complex Function MeasureTheory Set Zeta23
open scoped Convolution ContDiff Pointwise Polynomial SchwartzMap

noncomputable section

private theorem signed_measure_distribution_apply
    (epsilon : SignedMeasure ℝ) (test : 𝓢(ℝ, ℂ)) :
    (epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
        epsilon.toJordanDecomposition.negPart.toTemperedDistribution) test =
      ∫ᵛ u, test u ∂<•epsilon := by
  have hpos : epsilon.toJordanDecomposition.posPart.toSignedMeasure.Integrable
      (fun u => test u)
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    simp only [VectorMeasure.Integrable, VectorMeasure.variation_transpose_lsmul_flip,
      VectorMeasure.variation_toSignedMeasure]
    exact Integrable.of_bound test.continuous.aestronglyMeasurable
      ‖test.toBoundedContinuousFunction‖
      (ae_of_all _ test.toBoundedContinuousFunction.norm_coe_le_norm)
  have hneg : epsilon.toJordanDecomposition.negPart.toSignedMeasure.Integrable
      (fun u => test u)
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    simp only [VectorMeasure.Integrable, VectorMeasure.variation_transpose_lsmul_flip,
      VectorMeasure.variation_toSignedMeasure]
    exact Integrable.of_bound test.continuous.aestronglyMeasurable
      ‖test.toBoundedContinuousFunction‖
      (ae_of_all _ test.toBoundedContinuousFunction.norm_coe_le_norm)
  change (∫ u, test u ∂epsilon.toJordanDecomposition.posPart) -
      (∫ u, test u ∂epsilon.toJordanDecomposition.negPart) = _
  conv_rhs =>
    rw [← epsilon.toSignedMeasure_toJordanDecomposition,
      JordanDecomposition.toSignedMeasure,
      VectorMeasure.integral_sub_vectorMeasure hpos hneg]
  simp

private theorem iterated_deriv_delta_apply (j : ℕ) (b : ℝ) (test : 𝓢(ℝ, ℂ)) :
    ((TemperedDistribution.derivCLM ℂ)^[j] (TemperedDistribution.delta b)) test =
      (-1 : ℂ) ^ j * ((SchwartzMap.derivCLM ℂ ℂ)^[j] test) b := by
  induction j generalizing test with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', TemperedDistribution.derivCLM_apply_apply, ih]
      simp only [iterate_map_neg, neg_apply]
      rw [Function.iterate_succ_apply]
      simp [pow_succ]

private theorem signed_measure_integrable_of_jordan_restrict_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (epsilon : SignedMeasure ℝ) {s : Set ℝ} (hsCompact : IsCompact s)
    (hpos : epsilon.toJordanDecomposition.posPart.restrict s =
      epsilon.toJordanDecomposition.posPart)
    (hneg : epsilon.toJordanDecomposition.negPart.restrict s =
      epsilon.toJordanDecomposition.negPart)
    {g : ℝ → E} (hg : ContinuousOn g s) :
    epsilon.Integrable g (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
  have hposInt : Integrable g epsilon.toJordanDecomposition.posPart := by
    rw [← hpos]
    exact hg.integrableOn_compact hsCompact
  have hnegInt : Integrable g epsilon.toJordanDecomposition.negPart := by
    rw [← hneg]
    exact hg.integrableOn_compact hsCompact
  have hposSigned : epsilon.toJordanDecomposition.posPart.toSignedMeasure.Integrable g
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    simpa only [VectorMeasure.Integrable, VectorMeasure.variation_transpose_lsmul_flip,
      VectorMeasure.variation_toSignedMeasure] using hposInt
  have hnegSigned : epsilon.toJordanDecomposition.negPart.toSignedMeasure.Integrable g
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    simpa only [VectorMeasure.Integrable, VectorMeasure.variation_transpose_lsmul_flip,
      VectorMeasure.variation_toSignedMeasure] using hnegInt
  rw [← epsilon.toSignedMeasure_toJordanDecomposition, JordanDecomposition.toSignedMeasure]
  exact hposSigned.sub_vectorMeasure hnegSigned

private theorem eval_eq_sum_hasseDeriv_mul_sub_pow
    (K : ℕ) (p : ℝ[X]) (b u : ℝ) (hp : p.natDegree ≤ K) :
    p.eval u = ∑ j ∈ Finset.range (K + 1),
      (Polynomial.hasseDeriv j p).eval b * (u - b) ^ j := by
  calc
    p.eval u =
        (((Polynomial.taylor b p).sum fun j a =>
          Polynomial.C a * (Polynomial.X - Polynomial.C b) ^ j).eval u) := by
      rw [Polynomial.sum_taylor_eq]
    _ = ∑ j ∈ (Polynomial.taylor b p).support,
        (Polynomial.hasseDeriv j p).eval b * (u - b) ^ j := by
      simp only [Polynomial.sum_def, Polynomial.eval_finsetSum, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
      simp_rw [Polynomial.taylor_coeff]
    _ = ∑ j ∈ Finset.range (K + 1),
        (Polynomial.hasseDeriv j p).eval b * (u - b) ^ j := by
      apply Finset.sum_subset
      · intro j hj
        rw [Finset.mem_range]
        exact lt_of_le_of_lt
            ((Polynomial.le_natDegree_of_ne_zero
              (Polynomial.mem_support_iff.mp hj)).trans
            ((Polynomial.natDegree_taylor p b).trans_le hp))
          (Nat.lt_succ_self K)
      · intro j _ hj
        have hjzero : (Polynomial.taylor b p).coeff j = 0 := by
          simpa [Polynomial.mem_support_iff] using hj
        rw [← Polynomial.taylor_coeff, hjzero, zero_mul]

private theorem iterated_deriv_eq_zero_of_notMem_tsupport
    (j : ℕ) (test : 𝓢(ℝ, ℂ)) (x : ℝ) (hx : x ∉ tsupport test) :
    ((SchwartzMap.derivCLM ℂ ℂ)^[j] test) x = 0 := by
  have hsupport : tsupport ((SchwartzMap.derivCLM ℂ ℂ)^[j] test) ⊆ tsupport test := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact (SchwartzMap.tsupport_derivCLM_subset ℂ _).trans ih
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport h))

private theorem signed_measure_integral_polynomial_eq_sum
    (K : ℕ) (epsilon : SignedMeasure ℝ) (b : ℝ)
    (hpos : epsilon.toJordanDecomposition.posPart.restrict (Icc 0 b) =
      epsilon.toJordanDecomposition.posPart)
    (hneg : epsilon.toJordanDecomposition.negPart.restrict (Icc 0 b) =
      epsilon.toJordanDecomposition.negPart)
    (p : ℝ[X]) (hp : p.natDegree ≤ K) :
    (∫ᵛ u, p.eval u ∂<•epsilon) =
      ∑ j ∈ Finset.range (K + 1),
        (Polynomial.hasseDeriv j p).eval b * (∫ᵛ u, (u - b) ^ j ∂<•epsilon) := by
  have hpower (j : ℕ) : epsilon.Integrable (fun u => (u - b) ^ j)
      (ContinuousLinearMap.lsmul ℝ ℝ).flip :=
    signed_measure_integrable_of_jordan_restrict_eq epsilon isCompact_Icc hpos hneg
      (by fun_prop)
  have hterm (j : ℕ) : epsilon.Integrable
      (fun u => (Polynomial.hasseDeriv j p).eval b * (u - b) ^ j)
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    convert (hpower j).smul ((Polynomial.hasseDeriv j p).eval b) using 1
    ext u
    simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∫ᵛ u, p.eval u ∂<•epsilon) =
        ∫ᵛ u, ∑ j ∈ Finset.range (K + 1),
          (Polynomial.hasseDeriv j p).eval b * (u - b) ^ j ∂<•epsilon := by
      congr 1
      funext u
      exact eval_eq_sum_hasseDeriv_mul_sub_pow K p b u hp
    _ = ∑ j ∈ Finset.range (K + 1),
        ∫ᵛ u, (Polynomial.hasseDeriv j p).eval b * (u - b) ^ j ∂<•epsilon := by
      exact VectorMeasure.integral_finsetSum _ fun j _ => hterm j
    _ = ∑ j ∈ Finset.range (K + 1),
        (Polynomial.hasseDeriv j p).eval b * (∫ᵛ u, (u - b) ^ j ∂<•epsilon) := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [smul_eq_mul] using VectorMeasure.integral_fun_smul
        epsilon (ContinuousLinearMap.lsmul ℝ ℝ).flip
        ((Polynomial.hasseDeriv j p).eval b) (fun u => (u - b) ^ j)

private theorem corrected_polynomial_action_eq_zero
    (K : ℕ) (epsilon : SignedMeasure ℝ) (b : ℝ)
    (hpos : epsilon.toJordanDecomposition.posPart.restrict (Icc 0 b) =
      epsilon.toJordanDecomposition.posPart)
    (hneg : epsilon.toJordanDecomposition.negPart.restrict (Icc 0 b) =
      epsilon.toJordanDecomposition.negPart)
    (p : ℝ[X]) (hp : p.natDegree ≤ K) :
    (∫ᵛ u, p.eval u ∂<•epsilon) +
        ∑ j ∈ Finset.range (K + 1),
          ((-1 : ℝ) ^ (j + 1) * (∫ᵛ u, (u - b) ^ j ∂<•epsilon) / j.factorial) *
            ((-1 : ℝ) ^ j * (Polynomial.derivative^[j] p).eval b) = 0 := by
  rw [signed_measure_integral_polynomial_eq_sum K epsilon b hpos hneg p hp,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have hderiv : (Polynomial.derivative^[j] p).eval b =
      (j.factorial : ℝ) * (Polynomial.hasseDeriv j p).eval b := by
    have hpoly := congrFun
      (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := j)) p
    change j.factorial • Polynomial.hasseDeriv j p =
      Polynomial.derivative^[j] p at hpoly
    have h := congrArg (Polynomial.eval b) hpoly
    simpa only [map_nsmul, nsmul_eq_mul, Polynomial.eval_natCast_mul] using h.symm
  have hsign : (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ j = -1 := by
    calc
      (-1 : ℝ) ^ (j + 1) * (-1 : ℝ) ^ j =
          -(((-1 : ℝ) ^ j) ^ 2) := by rw [pow_succ]; ring
      _ = -1 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have hfactorial : (j.factorial : ℝ) ≠ 0 := by positivity
  rw [hderiv]
  field_simp
  rw [hsign]
  ring

private theorem corrected_distribution_apply
    (K : ℕ) (epsilon : SignedMeasure ℝ) (b : ℝ) (test : 𝓢(ℝ, ℂ)) :
    ((epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
          epsilon.toJordanDecomposition.negPart.toTemperedDistribution) +
        ∑ j ∈ Finset.range (K + 1),
          ((((-1 : ℝ) ^ (j + 1) *
              (∫ᵛ u, (u - b) ^ j ∂<•epsilon) / j.factorial : ℝ) : ℂ) •
            (TemperedDistribution.derivCLM ℂ)^[j]
              (TemperedDistribution.delta b))) test =
      (∫ᵛ u, test u ∂<•epsilon) +
        ∑ j ∈ Finset.range (K + 1),
          ((((-1 : ℝ) ^ (j + 1) *
              (∫ᵛ u, (u - b) ^ j ∂<•epsilon) / j.factorial : ℝ) : ℂ) *
            ((-1 : ℂ) ^ j * ((SchwartzMap.derivCLM ℂ ℂ)^[j] test) b)) := by
  change (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test)
      ((epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
          epsilon.toJordanDecomposition.negPart.toTemperedDistribution) + _) = _
  have hbase :
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test)
        (epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
          epsilon.toJordanDecomposition.negPart.toTemperedDistribution) =
        ∫ᵛ u, test u ∂<•epsilon := by
    change (epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
      epsilon.toJordanDecomposition.negPart.toTemperedDistribution) test = _
    exact signed_measure_distribution_apply epsilon test
  rw [map_add, hbase]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hdelta :
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test)
        ((TemperedDistribution.derivCLM ℂ)^[j] (TemperedDistribution.delta b)) =
      (-1 : ℂ) ^ j * ((SchwartzMap.derivCLM ℂ ℂ)^[j] test) b := by
    change ((TemperedDistribution.derivCLM ℂ)^[j]
      (TemperedDistribution.delta b)) test = _
    exact iterated_deriv_delta_apply j b test
  rw [map_smul, hdelta]
  simp only [smul_eq_mul]

private theorem weilTest_tsupport_subset_Ioo
    (L : ℝ) (f h : ℝ → ℂ)
    (hfCompact : HasCompactSupport f) (hhCompact : HasCompactSupport h)
    (hfSupport : tsupport f ⊆ Ioo (-L) L)
    (hhSupport : tsupport h ⊆ Ioo (-L) L) :
    tsupport (EF.weilTest f h) ⊆ Ioo (-(2 * L)) (2 * L) := by
  have hclosed : IsClosed (tsupport f + -tsupport h) :=
    (hfCompact.isCompact.add hhCompact.isCompact.neg).isClosed
  refine (closure_minimal ((support_convolution_subset _).trans ?_) hclosed).trans ?_
  · rintro x ⟨a, ha, c, hc, rfl⟩
    exact ⟨a, subset_tsupport f ha, c, EF.support_tilde_subset h hc, rfl⟩
  · rintro x ⟨a, ha, c, hc, rfl⟩
    have ha' := hfSupport ha
    have hc' := hhSupport (Set.mem_neg.mp hc)
    simp only [mem_Ioo] at ha' hc' ⊢
    constructor <;> linarith

/-- The canonical endpoint delta jet removes the first `K + 1` centered moments of a compactly
supported signed measure, while its action on every Weil correlation remains unchanged. -/
theorem finite_moment_elimination
    (L : ℝ) (K : ℕ) (epsilon : SignedMeasure ℝ)
    (hpos : epsilon.toJordanDecomposition.posPart.restrict (Icc 0 (2 * L)) =
      epsilon.toJordanDecomposition.posPart)
    (hneg : epsilon.toJordanDecomposition.negPart.restrict (Icc 0 (2 * L)) =
      epsilon.toJordanDecomposition.negPart)
    (f h : ℝ → ℂ) (hfSmooth : ContDiff ℝ ∞ f) (hhSmooth : ContDiff ℝ ∞ h)
    (hfCompact : HasCompactSupport f) (hhCompact : HasCompactSupport h)
    (hfSupport : tsupport f ⊆ Ioo (-L) L) (hhSupport : tsupport h ⊆ Ioo (-L) L) :
    let b := 2 * L
    let moment : ℕ → ℝ := fun j => ∫ᵛ u, (u - b) ^ j ∂<•epsilon
    let measureDistribution : 𝓢'(ℝ, ℂ) :=
      epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
        epsilon.toJordanDecomposition.negPart.toTemperedDistribution
    let correction : 𝓢'(ℝ, ℂ) :=
      ∑ j ∈ Finset.range (K + 1),
        ((((-1 : ℝ) ^ (j + 1) * moment j / j.factorial : ℝ) : ℂ) •
          (TemperedDistribution.derivCLM ℂ)^[j] (TemperedDistribution.delta b))
    let correctedDistribution := measureDistribution + correction
    let correlation := EF.weilTest f h
    let hcorrelationCompact : HasCompactSupport correlation :=
      EF.weilTest_hasCompactSupport hfCompact hhCompact
    let hcorrelationSmooth : ContDiff ℝ ∞ correlation :=
      (by
        have htildeSmooth : ContDiff ℝ ∞ (EF.tilde h) :=
          Complex.conjCLE.contDiff.comp (hhSmooth.comp contDiff_neg)
        exact (EF.hasCompactSupport_tilde hhCompact).contDiff_convolution_right
          (n := (⊤ : ℕ∞)) (ContinuousLinearMap.mul ℝ ℂ)
          hfSmooth.continuous.locallyIntegrable htildeSmooth)
    let correlationTest := hcorrelationCompact.toSchwartzMap hcorrelationSmooth
    (∀ test : 𝓢(ℝ, ℂ),
      correctedDistribution test =
        (∫ᵛ u, test u ∂<•epsilon) +
          ∑ j ∈ Finset.range (K + 1),
            ((((-1 : ℝ) ^ (j + 1) * moment j / j.factorial : ℝ) : ℂ) *
              ((-1 : ℂ) ^ j * ((SchwartzMap.derivCLM ℂ ℂ)^[j] test) b))) ∧
    (∀ p : ℝ[X], p.natDegree ≤ K →
      (∫ᵛ u, p.eval u ∂<•epsilon) +
          ∑ j ∈ Finset.range (K + 1),
            ((-1 : ℝ) ^ (j + 1) * moment j / j.factorial) *
              ((-1 : ℝ) ^ j * (Polynomial.derivative^[j] p).eval b) = 0) ∧
      correctedDistribution correlationTest = measureDistribution correlationTest := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact corrected_distribution_apply K epsilon (2 * L)
  · intro p hp
    exact corrected_polynomial_action_eq_zero K epsilon (2 * L) hpos hneg p hp
  · have hcorrelationSupport :
        tsupport (EF.weilTest f h) ⊆ Ioo (-(2 * L)) (2 * L) :=
      weilTest_tsupport_subset_Ioo L f h hfCompact hhCompact hfSupport hhSupport
    let correlationTest : 𝓢(ℝ, ℂ) :=
      (EF.weilTest_hasCompactSupport hfCompact hhCompact).toSchwartzMap (by
        have htildeSmooth : ContDiff ℝ ∞ (EF.tilde h) :=
          by exact Complex.conjCLE.contDiff.comp (hhSmooth.comp contDiff_neg)
        exact (EF.hasCompactSupport_tilde hhCompact).contDiff_convolution_right
          (n := (⊤ : ℕ∞)) (ContinuousLinearMap.mul ℝ ℂ)
          hfSmooth.continuous.locallyIntegrable htildeSmooth)
    have hb : 2 * L ∉ tsupport correlationTest := by
      intro hb
      exact (hcorrelationSupport hb).2.false
    have hjet (j : ℕ) :
        ((SchwartzMap.derivCLM ℂ ℂ)^[j] correlationTest) (2 * L) = 0 :=
      iterated_deriv_eq_zero_of_notMem_tsupport j correlationTest (2 * L) hb
    have hcorrection :
        (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ correlationTest)
          (∑ j ∈ Finset.range (K + 1),
          ((((-1 : ℝ) ^ (j + 1) *
              (∫ᵛ u, (u - 2 * L) ^ j ∂<•epsilon) / j.factorial : ℝ) : ℂ) •
            (TemperedDistribution.derivCLM ℂ)^[j]
              (TemperedDistribution.delta (2 * L)))) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      have hdelta :
          (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ correlationTest)
            ((TemperedDistribution.derivCLM ℂ)^[j]
              (TemperedDistribution.delta (2 * L))) = 0 := by
        change ((TemperedDistribution.derivCLM ℂ)^[j]
          (TemperedDistribution.delta (2 * L))) correlationTest = 0
        rw [iterated_deriv_delta_apply, hjet j, mul_zero]
      rw [map_smul, hdelta, smul_zero]
    change
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ correlationTest)
        ((epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
            epsilon.toJordanDecomposition.negPart.toTemperedDistribution) +
        (∑ j ∈ Finset.range (K + 1),
          ((((-1 : ℝ) ^ (j + 1) *
              (∫ᵛ u, (u - 2 * L) ^ j ∂<•epsilon) / j.factorial : ℝ) : ℂ) •
            (TemperedDistribution.derivCLM ℂ)^[j]
              (TemperedDistribution.delta (2 * L))))) =
      (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ correlationTest)
        (epsilon.toJordanDecomposition.posPart.toTemperedDistribution -
          epsilon.toJordanDecomposition.negPart.toTemperedDistribution)
    rw [map_add, hcorrection, add_zero]

#print axioms finite_moment_elimination

end

end D5.S3.Weil.TestFunctions.FiniteMomentElimination
