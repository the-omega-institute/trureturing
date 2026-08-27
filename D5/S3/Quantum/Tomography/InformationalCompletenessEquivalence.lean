/- GID: D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/InformationalCompletenessEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Centered quantum readout completeness has four equivalent linear forms. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.TFAE

/- Library-search audit trail (2026-08-27):
   * Exact family hits HermitianSpace, traceZeroHermitian, identityHermitian, and
     scalarHermitian supply the source's real full and traceless Hermitian carriers.
   * Exact pinned-Mathlib hits Submodule.orthogonal_eq_bot_iff,
     Submodule.finrank_map_subtype_eq, Submodule.eq_top_of_disjoint, and
     Submodule.eq_top_of_finrank_eq are applied directly.
   * Repository searches found per-pair readout/residual equivalences, but no theorem exposing
     all four global completeness clauses on these canonical carriers. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

private theorem hermitian_trace_eq_re {d : Nat} (A : HermitianSpace d) :
    Matrix.trace A.1 = ((Matrix.trace A.1).re : ℂ) := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  have hstar : star (Matrix.trace A.1) = Matrix.trace A.1 := by
    calc
      star (Matrix.trace A.1) = Matrix.trace A.1ᴴ :=
        (Matrix.trace_conjTranspose A.1).symm
      _ = Matrix.trace A.1 := by rw [hA]
  exact (Complex.conj_eq_iff_re.mp hstar).symm

private theorem hermitian_inner_identity {d : Nat} (A : HermitianSpace d) :
    inner ℝ A (identityHermitian d) = (Matrix.trace A.1).re := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  change (Matrix.trace ((1 : Matrix (Fin d) (Fin d) ℂ) * 1 * A.1ᴴ)).re = _
  rw [one_mul, one_mul, hA]

private theorem trace_zero_eq_scalar_orthogonal (d : Nat) :
    traceZeroHermitian d = (scalarHermitian d)ᗮ := by
  ext A
  change Matrix.trace A.1 = 0 ↔ A ∈ (scalarHermitian d)ᗮ
  rw [scalarHermitian, Submodule.mem_orthogonal_singleton_iff_inner_left,
    hermitian_inner_identity]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    rw [hermitian_trace_eq_re A, h]
    rfl

private theorem analysis_injective_iff_span_eq_top
    {E Index : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (vectors : Index -> E) :
    Function.Injective (fun X => fun i => inner ℝ X (vectors i)) ↔
      Submodule.span ℝ (Set.range vectors) = ⊤ := by
  let visible := Submodule.span ℝ (Set.range vectors)
  constructor
  · intro hinjective
    apply (Submodule.orthogonal_eq_bot_iff).mp
    ext X
    constructor
    · intro hX
      have hreadout :
          (fun i => inner ℝ X (vectors i)) =
            fun i => inner ℝ (0 : E) (vectors i) := by
        funext i
        have hgenerator : vectors i ∈ visible :=
          Submodule.subset_span (Set.mem_range_self i)
        have hzero := (Submodule.mem_orthogonal' visible X).mp hX
          (vectors i) hgenerator
        simpa using hzero
      have hXzero := hinjective hreadout
      simp [hXzero]
    · intro hX
      have hXzero : X = 0 := by simpa using hX
      subst X
      exact Submodule.zero_mem _
  · intro hvisible X Y hreadout
    have hdifference : X - Y ∈ visibleᗮ := by
      rw [Submodule.mem_orthogonal']
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem Z hgenerator =>
          rcases hgenerator with ⟨i, rfl⟩
          have hi := congrFun hreadout i
          simpa [inner_sub_left, sub_eq_zero] using hi
      | zero => simp
      | add first second _ _ hfirst hsecond =>
          simp only [inner_add_right, hfirst, hsecond, add_zero]
      | smul scalar Z _ hZ =>
          simp only [real_inner_smul_right, hZ, mul_zero]
    change X - Y ∈ (Submodule.span ℝ (Set.range vectors))ᗮ at hdifference
    rw [hvisible, Submodule.top_orthogonal_eq_bot] at hdifference
    exact sub_eq_zero.mp hdifference

private theorem trace_zero_inner_eq_trace
    {d : Nat} (A B : traceZeroHermitian d) :
    inner ℝ A B = (Matrix.trace (A.1.1 * B.1.1)).re := by
  have hAstar := A.1.2
  change star A.1.1 = A.1.1 at hAstar
  have hA : A.1.1ᴴ = A.1.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  change (Matrix.trace (B.1.1 * 1 * A.1.1ᴴ)).re = _
  rw [Matrix.mul_one, hA, Matrix.trace_mul_comm]

private theorem density_signature_injective_iff_analysis_injective
    (d : Nat) [NeZero d] {Index : Type*}
    (centeredEffects : Index -> traceZeroHermitian d) :
    Function.Injective (fun rho : DensityState (Fin d) => fun i =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (centeredEffects i).1.1)).re) ↔
      Function.Injective (fun X => fun i => inner ℝ X (centeredEffects i)) := by
  let stateSignature := fun rho : DensityState (Fin d) => fun i =>
    (Matrix.trace
      (CStarMatrix.ofMatrix.symm rho.1 * (centeredEffects i).1.1)).re
  let analysis := fun X : traceZeroHermitian d => fun i =>
    inner ℝ X (centeredEffects i)
  constructor
  · intro hphysical X Y hreadout
    let D : traceZeroHermitian d := X - Y
    let A : CStarMatrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix D.1.1
    let c : ℝ := (d : ℝ)⁻¹
    let eps : ℝ := c / (2 * (‖A‖ + 1))
    have hc : 0 < c :=
      inv_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
    have hdenominator : 0 < 2 * (‖A‖ + 1) :=
      mul_pos (by norm_num) (by positivity)
    have heps : 0 < eps := div_pos hc hdenominator
    have hproduct : eps * (‖A‖ + 1) = c / 2 := by
      dsimp only [eps]
      field_simp
    have hcoefficient : 0 ≤ c - eps * ‖A‖ := by
      have hstrict : eps * ‖A‖ < eps * (‖A‖ + 1) := by nlinarith
      rw [hproduct] at hstrict
      linarith
    have hAself : IsSelfAdjoint A := by
      exact congrArg CStarMatrix.ofMatrix D.1.2
    have hlower :=
      IsSelfAdjoint.neg_algebraMap_norm_le_self (a := A) (ha := hAself)
    have hlowerScaled := smul_le_smul_of_nonneg_left hlower heps.le
    have hlowerShifted := add_le_add_left hlowerScaled
      ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)
    have hpositiveLeft :
        0 ≤ eps •
              (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖) +
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c := by
      have heq :
          eps •
                (-(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖) +
              (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c =
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ))
              (c - eps * ‖A‖) := by
        simp only [map_sub, map_mul, Algebra.smul_def]
        noncomm_ring
      rw [heq]
      exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ)
        hcoefficient
    have hplus :
        0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A := by
      have hresult := hpositiveLeft.trans hlowerShifted
      rw [add_comm (eps • A)
        ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)] at hresult
      simpa only [Algebra.smul_def] using hresult
    have hupper :=
      IsSelfAdjoint.le_algebraMap_norm_self (a := A) (ha := hAself)
    have hupperScaled := smul_le_smul_of_nonneg_left hupper heps.le
    have hpositiveBase :
        0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
          eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖ := by
      have heq :
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
              eps • (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) ‖A‖ =
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ))
              (c - eps * ‖A‖) := by
        simp only [map_sub, map_mul, Algebra.smul_def]
      rw [heq]
      exact algebraMap_nonneg (β := CStarMatrix (Fin d) (Fin d) ℂ)
        hcoefficient
    have hminus :
        0 ≤ (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A := by
      have hbound := sub_le_sub_left hupperScaled
        ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c)
      simp only [Algebra.smul_def] at hpositiveBase hbound ⊢
      exact hpositiveBase.trans hbound
    have hmatrixPlus :
        CStarMatrix.ofMatrix.symm
            ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
              (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) =
          (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
            (eps : ℂ) • D.1.1 := by
      ext i j
      simp [A, Algebra.smul_def, CStarMatrix.algebraMap_apply,
        Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
    have hmatrixMinus :
        CStarMatrix.ofMatrix.symm
            ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
              (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A) =
          (c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) -
            (eps : ℂ) • D.1.1 := by
      ext i j
      simp [A, Algebra.smul_def, CStarMatrix.algebraMap_apply,
        Matrix.algebraMap_matrix_apply, CStarMatrix.mul_apply, Matrix.mul_apply]
    have htracePlus :
        Matrix.trace
            (CStarMatrix.ofMatrix.symm
              ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
                (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A)) = 1 := by
      rw [hmatrixPlus]
      have hDtrace : Matrix.trace D.1.1 = 0 := D.2
      have hcComplex : (c : ℂ) = (d : ℂ)⁻¹ := by
        dsimp only [c]
        exact Complex.ofReal_inv (d : ℝ)
      simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
        hDtrace, Fintype.card_fin, smul_eq_mul]
      rw [hcComplex]
      simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
    have htraceMinus :
        Matrix.trace
            (CStarMatrix.ofMatrix.symm
              ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
                (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A)) = 1 := by
      rw [hmatrixMinus]
      have hDtrace : Matrix.trace D.1.1 = 0 := D.2
      have hcComplex : (c : ℂ) = (d : ℂ)⁻¹ := by
        dsimp only [c]
        exact Complex.ofReal_inv (d : ℝ)
      simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
        hDtrace, Fintype.card_fin, smul_eq_mul]
      rw [hcComplex]
      simp [show (d : ℂ) ≠ 0 by exact_mod_cast NeZero.ne d]
    let rhoPlus : DensityState (Fin d) :=
      ⟨(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c +
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A,
        hplus, htracePlus⟩
    let rhoMinus : DensityState (Fin d) :=
      ⟨(algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c -
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) eps * A,
        hminus, htraceMinus⟩
    have hstateReadout : stateSignature rhoPlus = stateSignature rhoMinus := by
      funext i
      have hDreadout : inner ℝ D (centeredEffects i) = 0 := by
        have hi := congrFun hreadout i
        dsimp only [analysis] at hi
        simpa only [D, inner_sub_left, sub_eq_zero] using hi
      rw [trace_zero_inner_eq_trace] at hDreadout
      dsimp only [stateSignature, rhoPlus, rhoMinus]
      rw [hmatrixPlus, hmatrixMinus]
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul,
        Matrix.one_mul, Matrix.trace_add, Matrix.trace_sub,
        Matrix.trace_smul, Complex.add_re, Complex.sub_re]
      have hscaledReadout :
          ((eps : ℂ) • Matrix.trace (D.1.1 * (centeredEffects i).1.1)).re = 0 := by
        rw [smul_eq_mul, Complex.mul_re]
        simp [hDreadout]
      rw [hscaledReadout]
      ring
    have hstates : rhoPlus = rhoMinus := hphysical hstateReadout
    have hvalues := congrArg (fun rho : DensityState (Fin d) => rho.1) hstates
    have hdifference : (2 * eps : ℝ) • A = 0 := by
      dsimp only [rhoPlus, rhoMinus] at hvalues
      have hvalues' :
          (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c + eps • A =
            (algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c - eps • A := by
        simpa only [Algebra.smul_def] using hvalues
      calc
        (2 * eps : ℝ) • A = 2 • (eps • A) :=
          (smul_smul (2 : ℝ) eps A).symm
        _ = eps • A + eps • A := two_smul ℝ (eps • A)
        _ = ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c + eps • A) -
            ((algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ)) c - eps • A) := by
          abel
        _ = 0 := sub_eq_zero.mpr hvalues'
    have hAzero : A = 0 := by
      exact (smul_eq_zero.mp hdifference).resolve_left (by positivity)
    have hDzero : D = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      apply CStarMatrix.ofMatrix.injective
      exact hAzero.trans
        (show (0 : CStarMatrix (Fin d) (Fin d) ℂ) =
          CStarMatrix.ofMatrix (0 : Matrix (Fin d) (Fin d) ℂ) from rfl)
    exact sub_eq_zero.mp hDzero
  · intro hanalysis rho sigma hreadout
    let D : traceZeroHermitian d :=
      ⟨⟨CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1,
        by
          have hrho : (CStarMatrix.ofMatrix.symm rho.1).IsHermitian :=
            congrArg CStarMatrix.ofMatrix.symm rho.2.1.isSelfAdjoint.star_eq
          have hsigma : (CStarMatrix.ofMatrix.symm sigma.1).IsHermitian :=
            congrArg CStarMatrix.ofMatrix.symm sigma.2.1.isSelfAdjoint.star_eq
          exact hrho.sub hsigma⟩,
        by
          change Matrix.trace
            (CStarMatrix.ofMatrix.symm rho.1 -
              CStarMatrix.ofMatrix.symm sigma.1) = 0
          have hrhoTrace : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 :=
            rho.2.2
          have hsigmaTrace : Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1) = 1 :=
            sigma.2.2
          rw [Matrix.trace_sub, hrhoTrace, hsigmaTrace, sub_self]⟩
    have hDreadout : analysis D = analysis 0 := by
      funext i
      have hi := congrFun hreadout i
      dsimp only [stateSignature] at hi
      dsimp only [analysis]
      rw [trace_zero_inner_eq_trace, trace_zero_inner_eq_trace]
      simp only [Submodule.coe_zero, zero_mul,
        Matrix.trace_zero, Complex.zero_re]
      dsimp only [D]
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, sub_eq_zero]
      exact hi
    have hDzero := hanalysis hDreadout
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    have := congrArg (fun Z : traceZeroHermitian d => Z.1.1) hDzero
    simpa only [D, Submodule.coe_zero, Subtype.coe_mk, sub_eq_zero] using this

private theorem visible_top_iff_centered_top
    (d : Nat) [NeZero d]
    (centeredVisible : Submodule ℝ (traceZeroHermitian d)) :
    scalarHermitian d ⊔
        centeredVisible.map (traceZeroHermitian d).subtype = ⊤ ↔
      centeredVisible = ⊤ := by
  let mapped :=
    centeredVisible.map (traceZeroHermitian d).subtype
  have hmapped : mapped ≤ traceZeroHermitian d := by
    rintro _ ⟨X, hX, rfl⟩
    exact X.2
  have horthogonal : scalarHermitian d ⟂ mapped := by
    rw [trace_zero_eq_scalar_orthogonal d] at hmapped
    exact (Submodule.isOrtho_orthogonal_right (scalarHermitian d)).mono_right hmapped
  have hdisjoint : Disjoint (scalarHermitian d) mapped := horthogonal.disjoint
  have hscalarRank : Module.finrank ℝ (scalarHermitian d) = 1 := by
    apply finrank_span_singleton
    intro hzero
    have hvalue : (1 : Matrix (Fin d) (Fin d) ℂ) = 0 :=
      congrArg Subtype.val hzero
    exact one_ne_zero hvalue
  have hmappedRank :
      Module.finrank ℝ mapped = Module.finrank ℝ centeredVisible := by
    exact Submodule.finrank_map_subtype_eq _ _
  constructor
  · intro hvisible
    change scalarHermitian d ⊔ mapped = ⊤ at hvisible
    have hlower :
        Module.finrank ℝ (HermitianSpace d) ≤
          Module.finrank ℝ (scalarHermitian d) +
            Module.finrank ℝ mapped := by
      calc
        Module.finrank ℝ (HermitianSpace d) =
            Module.finrank ℝ (⊤ : Submodule ℝ (HermitianSpace d)) := by
          rw [finrank_top]
        _ = Module.finrank ℝ
            (scalarHermitian d ⊔ mapped : Submodule ℝ (HermitianSpace d)) := by
          rw [hvisible]
        _ ≤ Module.finrank ℝ (scalarHermitian d) +
              Module.finrank ℝ mapped :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
    have hcenteredUpper :
        Module.finrank ℝ centeredVisible ≤ d ^ 2 - 1 := by
      calc
        Module.finrank ℝ centeredVisible ≤
            Module.finrank ℝ (traceZeroHermitian d) :=
          Submodule.finrank_le _
        _ = d ^ 2 - 1 := trace_zero_hermitian_finrank d
    have hcenteredRank :
        Module.finrank ℝ centeredVisible =
          Module.finrank ℝ (traceZeroHermitian d) := by
      rw [hermitian_space_finrank, hscalarRank, hmappedRank] at hlower
      rw [trace_zero_hermitian_finrank d]
      omega
    exact Submodule.eq_top_of_finrank_eq hcenteredRank
  · intro hcentered
    apply Submodule.eq_top_of_disjoint _ _ _ hdisjoint
    rw [hermitian_space_finrank, hscalarRank, hmappedRank, hcentered,
      finrank_top, trace_zero_hermitian_finrank d]
    have hdPositive : 0 < d ^ 2 := pow_pos (Nat.pos_of_ne_zero (NeZero.ne d)) 2
    omega

/-- For a centered finite-dimensional quantum observer, informational completeness,
trivial invisible residual, full visible Hermitian space, and full centered-effect span
are four equivalent conditions. -/
theorem informational_completeness_four_way
    (d : Nat) [NeZero d] {Index : Type*}
    (centeredEffects : Index -> traceZeroHermitian d) :
    let centeredVisible :=
      Submodule.span ℝ (Set.range centeredEffects)
    let visible :=
      scalarHermitian d ⊔
        centeredVisible.map (traceZeroHermitian d).subtype
    let residual := visibleᗮ
    List.TFAE [
      Function.Injective (fun rho : DensityState (Fin d) => fun i =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (centeredEffects i).1.1)).re),
      residual = ⊥,
      visible = ⊤,
      centeredVisible = ⊤
    ] := by
  dsimp only
  tfae_have 1 ↔ 4 :=
    (density_signature_injective_iff_analysis_injective d centeredEffects).trans
      (analysis_injective_iff_span_eq_top centeredEffects)
  tfae_have 2 ↔ 3 :=
    Submodule.orthogonal_eq_bot_iff
  tfae_have 3 ↔ 4 :=
    visible_top_iff_centered_top d
      (Submodule.span ℝ (Set.range centeredEffects))
  tfae_finish

#print axioms informational_completeness_four_way

end D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
