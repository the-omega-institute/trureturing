/- GID: D5/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/TraceZeroReadoutOrthogonalEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Real trace-zero Hermitian readout fibers equal residual and projection fibers. -/

import D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
import Mathlib.Analysis.InnerProductSpace.StandardSubspace

/- Library-search audit trail (2026-08-21):
   * Exact repository hit `FutureWordOrthogonalResidual.future_word_orthogonal_residual`
     supplies the residual/projection equivalence and is applied directly below.
   * Frozen family definitions `ReadoutOrthogonalEquivalence.centeredEffect`,
     `centeredState`, and `finiteTraceReadout` are imported rather than redeclared.
   * Pinned Mathlib exact hits `InnerProductSpace.rclikeToReal`,
     `Submodule.innerProductSpace`, `Submodule.starProjection`,
     `Matrix.trace_conjTranspose`, and `Matrix.trace_mul_comm` supply the real
     carrier and Hilbert-space bridge. No exact theorem packaging the source's
     four clauses on the trace-zero Hermitian carrier was found.
   * `loogle` and `leansearch` executables are absent from PATH. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix
open ClosedSubmodule

namespace D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence

open D5.S3.Quantum.Algebra.FutureWordOrthogonalResidual
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence

variable {d : Type*} [Fintype d] [Nonempty d] [DecidableEq d]

local instance matrixNormedAddCommGroup : NormedAddCommGroup (Matrix d d ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace : InnerProductSpace ℂ (Matrix d d ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

/-- The source carrier: real Hermitian trace-zero matrices. -/
def HermitianTraceZero : Submodule ℝ (Matrix d d ℂ) where
  carrier := {A | A.IsHermitian ∧ Matrix.trace A = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    exact ⟨hA.1.add hB.1, by simp [Matrix.trace_add, hA.2, hB.2]⟩
  smul_mem' := by
    intro r A hA
    refine ⟨hA.1.smul ?_, ?_⟩
    · simp [isSelfAdjoint_iff]
    · simp [Matrix.trace_smul, hA.2]

private lemma trace_is_real (A : Matrix d d ℂ) (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  have hstar : star (Matrix.trace A) = Matrix.trace A := by
    rw [← Matrix.trace_conjTranspose, hA.eq]
  have him := congrArg Complex.im hstar
  change ((starRingEnd ℂ) (Matrix.trace A)).im = _ at him
  rw [Complex.conj_im] at him
  linarith

private lemma trace_mul_im_zero (A B : Matrix d d ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hstar : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul, hB.eq, hA.eq, Matrix.trace_mul_comm]
  have him := congrArg Complex.im hstar
  change ((starRingEnd ℂ) (Matrix.trace (A * B))).im = _ at him
  rw [Complex.conj_im] at him
  linarith

private lemma matrix_inner_eq_trace_conjTranspose_mul (A B : Matrix d d ℂ) :
    ⟪A, B⟫_ℂ = Matrix.trace (Aᴴ * B) := by
  change Matrix.trace (B * 1 * Aᴴ) = Matrix.trace (Aᴴ * B)
  rw [mul_one, Matrix.trace_mul_comm]

private lemma matrix_inner_eq_trace_mul_of_hermitian (A B : Matrix d d ℂ)
    (hA : A.IsHermitian) :
    ⟪A, B⟫_ℂ = Matrix.trace (A * B) := by
  rw [matrix_inner_eq_trace_conjTranspose_mul, hA.eq]

private lemma real_inner_eq_trace_mul (A B : HermitianTraceZero (d := d)) :
    inner ℝ A B = (Matrix.trace (A.1 * B.1)).re := by
  change (inner ℂ A.1 B.1).re = _
  rw [matrix_inner_eq_trace_mul_of_hermitian A.1 B.1 A.2.1]

private lemma real_inner_eq_zero_iff_trace_mul_eq_zero
    (A B : HermitianTraceZero (d := d)) :
    inner ℝ A B = 0 ↔ Matrix.trace (A.1 * B.1) = 0 := by
  rw [real_inner_eq_trace_mul]
  constructor
  · intro h
    apply Complex.ext
    · simpa [h]
    · exact trace_mul_im_zero A.1 B.1 A.2.1 B.2.1
  · intro h
    exact congrArg Complex.re h

private lemma centered_state_sub (rho sigma : Matrix d d ℂ) :
    centeredState rho - centeredState sigma = rho - sigma := by
  simp [centeredState, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

private lemma trace_sub_mul_centered_effect (rho sigma effect : Matrix d d ℂ)
    (htraceRho : Matrix.trace rho = 1) (htraceSigma : Matrix.trace sigma = 1) :
    Matrix.trace ((rho - sigma) * centeredEffect effect) =
      Matrix.trace ((rho - sigma) * effect) := by
  rw [centeredEffect, mul_sub, Matrix.trace_sub]
  have hzero : Matrix.trace (rho - sigma) = 0 := by
    rw [Matrix.trace_sub, htraceRho, htraceSigma, sub_self]
  simp [hzero]

private lemma centered_effect_mem (effect : Matrix d d ℂ)
    (hEffect : effect.IsHermitian) :
    centeredEffect effect ∈ HermitianTraceZero (d := d) := by
  refine ⟨hEffect.sub ?_, ?_⟩
  · exact Matrix.IsHermitian.smul (by simp)
      (by
        rw [isSelfAdjoint_iff]
        have hreal : Matrix.trace effect = ((Matrix.trace effect).re : ℂ) := by
          apply Complex.ext <;> simp [trace_is_real effect hEffect]
        rw [hreal]
        simp)
  · simp only [centeredEffect, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one]
    change Matrix.trace effect -
      (Matrix.trace effect / (Fintype.card d : ℂ)) * Fintype.card d = 0
    field_simp [show (Fintype.card d : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]
    simp

private lemma centered_state_mem (rho : Matrix d d ℂ)
    (hRho : rho.IsHermitian) (hTrace : Matrix.trace rho = 1) :
    centeredState rho ∈ HermitianTraceZero (d := d) := by
  refine ⟨hRho.sub ?_, ?_⟩
  · exact Matrix.IsHermitian.smul (by simp) (by rw [isSelfAdjoint_iff]; simp)
  · simp only [centeredState, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one, hTrace]
    simp only [smul_eq_mul]
    field_simp [show (Fintype.card d : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero]
    simp

/-- On the real carrier, readout equality, vanishing trace pairings, residual
membership, and equal visible projections are equivalent. -/
theorem readout_fiber_orthogonal_equivalence
    {m : ℕ} (effect : Fin (m + 1) → Matrix d d ℂ)
    (rho sigma : Matrix d d ℂ)
    (hrho : rho.PosSemidef ∧ Matrix.trace rho = 1)
    (hsigma : sigma.PosSemidef ∧ Matrix.trace sigma = 1)
    (hEffects : ∀ i, (effect i).PosSemidef ∧ (1 - effect i).PosSemidef) :
    let centeredEffects : Fin (m + 1) → HermitianTraceZero (d := d) :=
      fun i => ⟨centeredEffect (effect i),
        centered_effect_mem (effect i) (hEffects i).1.isHermitian⟩
    let Xrho : HermitianTraceZero (d := d) :=
      ⟨centeredState rho, centered_state_mem rho hrho.1.isHermitian hrho.2⟩
    let Xsigma : HermitianTraceZero (d := d) :=
      ⟨centeredState sigma, centered_state_mem sigma hsigma.1.isHermitian hsigma.2⟩
    let V0 : Submodule ℝ (HermitianTraceZero (d := d)) :=
      Submodule.span ℝ (Set.range centeredEffects)
    let R0 : Submodule ℝ (HermitianTraceZero (d := d)) := V0ᗮ
    (finiteTraceReadout effect rho = finiteTraceReadout effect sigma ↔
        ∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ∧
      ((∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ↔
        Xrho - Xsigma ∈ R0) ∧
      (Xrho - Xsigma ∈ R0 ↔
        V0.starProjection Xrho = V0.starProjection Xsigma) := by
  classical
  let centeredEffects : Fin (m + 1) → HermitianTraceZero (d := d) :=
    fun i => ⟨centeredEffect (effect i),
      centered_effect_mem (effect i) (hEffects i).1.isHermitian⟩
  let Xrho : HermitianTraceZero (d := d) :=
    ⟨centeredState rho, centered_state_mem rho hrho.1.isHermitian hrho.2⟩
  let Xsigma : HermitianTraceZero (d := d) :=
    ⟨centeredState sigma, centered_state_mem sigma hsigma.1.isHermitian hsigma.2⟩
  let V0 : Submodule ℝ (HermitianTraceZero (d := d)) :=
    Submodule.span ℝ (Set.range centeredEffects)
  let R0 : Submodule ℝ (HermitianTraceZero (d := d)) := V0ᗮ
  have htrace_iff_word :
      (∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ↔
        futureExpectationWord (𝕜 := ℝ) centeredEffects
            (fun state : Bool => if state then Xsigma else Xrho) false =
          futureExpectationWord (𝕜 := ℝ) centeredEffects
            (fun state : Bool => if state then Xsigma else Xrho) true := by
    constructor
    · intro htrace
      funext i
      have hinner : inner ℝ (Xrho - Xsigma) (centeredEffects i) = 0 := by
        apply (real_inner_eq_zero_iff_trace_mul_eq_zero _ _).2
        simpa [Xrho, Xsigma, centeredEffects, centered_state_sub,
          trace_sub_mul_centered_effect rho sigma (effect i) hrho.2 hsigma.2]
          using htrace i
      simpa [futureExpectationWord, inner_sub_left, sub_eq_zero] using hinner
    · intro hword i
      have hinner : inner ℝ (Xrho - Xsigma) (centeredEffects i) = 0 := by
        have hi := congrFun hword i
        simpa [futureExpectationWord, inner_sub_left, sub_eq_zero] using hi
      have hcomplex := (real_inner_eq_zero_iff_trace_mul_eq_zero _ _).1 hinner
      simpa [Xrho, Xsigma, centeredEffects, centered_state_sub,
        trace_sub_mul_centered_effect rho sigma (effect i) hrho.2 hsigma.2]
        using hcomplex
  have hcanonical :=
    future_word_orthogonal_residual
      (𝕜 := ℝ) (E := HermitianTraceZero (d := d)) (State := Bool)
      centeredEffects (fun state : Bool => if state then Xsigma else Xrho)
      false true
  change (finiteTraceReadout effect rho = finiteTraceReadout effect sigma ↔
      ∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ∧
    ((∀ i, Matrix.trace ((rho - sigma) * effect i) = 0) ↔
      Xrho - Xsigma ∈ R0) ∧
    (Xrho - Xsigma ∈ R0 ↔
      V0.starProjection Xrho = V0.starProjection Xsigma)
  constructor
  · constructor
    · intro hreadout i
      have hi := congrFun hreadout i
      simpa only [finiteTraceReadout, sub_mul, Matrix.trace_sub, sub_eq_zero] using hi
    · intro htrace
      funext i
      have hi := htrace i
      simpa only [finiteTraceReadout, sub_mul, Matrix.trace_sub, sub_eq_zero] using hi
  constructor
  · exact htrace_iff_word.trans hcanonical.1
  · exact hcanonical.2

#print axioms readout_fiber_orthogonal_equivalence

end D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
