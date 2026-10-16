/- GID: D5/S3/Observer/Linear/PrimeTimeGramianEnergyIdentity
   generality: I
   mirror-B: D5/B/S3/Observer/Linear/PrimeTimeGramianEnergyIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The weighted prime-time Gramian quadratic form equals trace-readout energy. -/

import D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
import D5.S3.Quantum.Measurement.BasisMeasurementProjection
import Mathlib.Analysis.InnerProductSpace.LinearMap

/- Library-search audit trail (2026-08-27):
   * The frozen discounted observability energy theorem has only one time
     stream and does not expose the source's five index families or trace-zero
     Hermitian carrier, so it is not an exact bind.
   * Canonical repository hits `centeredEffect`, `HermitianSpace`,
     `HermitianTraceZero`, and `primeEvidence` are imported and instantiated.
   * Exact pinned-Mathlib hits `ContinuousLinearMap.rankOne_apply`,
     `ContinuousLinearMap.map_tsum`, and `Complex.normSq_apply` supply the
     rank-one energy calculation. No packaged five-index identity was found. -/

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.PrimeTimeGramianEnergyIdentity

open D5.S3.Analytic.ZetaEntropyPlane.PrimeEvidenceSharpThreshold
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

variable {d : Nat} [NeZero d]

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

local instance hermitianTraceZeroTopologicalSpace :
    TopologicalSpace (HermitianTraceZero (d := Fin d)) :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

omit [NeZero d] in
private theorem trace_is_real (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) : (Matrix.trace A).im = 0 := by
  have hstar : star (Matrix.trace A) = Matrix.trace A := by
    rw [← Matrix.trace_conjTranspose, hA.eq]
  have him := congrArg Complex.im hstar
  change ((starRingEnd ℂ) (Matrix.trace A)).im = _ at him
  rw [Complex.conj_im] at him
  linarith

private theorem centered_effect_mem_trace_zero (effect : HermitianSpace d) :
    centeredEffect effect.1 ∈ HermitianTraceZero (d := Fin d) := by
  have hEffect : effect.1.IsHermitian := by
    have hstar := effect.2
    change star effect.1 = effect.1 at hstar
    change effect.1ᴴ = effect.1
    simpa only [Matrix.star_eq_conjTranspose] using hstar
  refine ⟨hEffect.sub ?_, ?_⟩
  · exact Matrix.IsHermitian.smul (by simp)
      (by
        rw [isSelfAdjoint_iff]
        have hreal : Matrix.trace effect.1 = ((Matrix.trace effect.1).re : ℂ) := by
          apply Complex.ext <;> simp [trace_is_real effect.1 hEffect]
        rw [hreal]
        simp)
  · simp only [centeredEffect, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_one]
    change Matrix.trace effect.1 -
      (Matrix.trace effect.1 / (Fintype.card (Fin d) : ℂ)) *
        Fintype.card (Fin d) = 0
    field_simp [show (Fintype.card (Fin d) : ℂ) ≠ 0 by
      exact_mod_cast Fintype.card_ne_zero]
    simp

omit [NeZero d] in
private theorem trace_mul_im_zero
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (A * B)).im = 0 := by
  have hstar : star (Matrix.trace (A * B)) = Matrix.trace (A * B) := by
    rw [← Matrix.trace_conjTranspose]
    rw [Matrix.conjTranspose_mul, hB.eq, hA.eq, Matrix.trace_mul_comm]
  have him := congrArg Complex.im hstar
  change ((starRingEnd ℂ) (Matrix.trace (A * B))).im = _ at him
  rw [Complex.conj_im] at him
  linarith

omit [NeZero d] in
private theorem matrix_inner_eq_trace_conjTranspose_mul
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    inner ℂ A B = Matrix.trace (Aᴴ * B) := by
  change Matrix.trace (B * 1 * Aᴴ) = Matrix.trace (Aᴴ * B)
  rw [mul_one, Matrix.trace_mul_comm]

omit [NeZero d] in
private theorem real_inner_eq_trace_mul
    (A B : HermitianTraceZero (d := Fin d)) :
    inner ℝ A B = (Matrix.trace (A.1 * B.1)).re := by
  change (inner ℂ A.1 B.1).re = _
  rw [matrix_inner_eq_trace_conjTranspose_mul, A.2.1.eq]

/-- For the source-constructed prime, precision, context, outcome, and time
weights, the quadratic form of the centered Heisenberg Gramian is exactly the
total squared trace-readout energy. -/
theorem prime_time_gramian_energy_identity
    {Context Outcome : Type*}
    (s beta : ℝ)
    (heisenberg : HermitianSpace d →ₗ[ℝ] HermitianSpace d)
    (effects : Nat.Primes → Nat → Context → Outcome → HermitianSpace d)
    (contextWeight : Context → Outcome → ℝ)
    (D : HermitianTraceZero (d := Fin d)) :
    let primePartition := ∑' p : Nat.Primes, primeEvidence s p
    let precisionWeight := fun (p : Nat.Primes) (k : Nat) =>
      (1 - primeEvidence s p) *
        (p.1 : ℝ) ^ (-s * ((k + 1 : Nat) : ℝ)) / primePartition
    let timeWeight := fun t : Nat => (1 - beta) * beta ^ t
    let centered := fun
        index : Nat.Primes × (Nat × (Context × (Outcome × Nat))) =>
      (⟨centeredEffect
          ((heisenberg ^ index.2.2.2.2)
            (effects index.1 index.2.1 index.2.2.1 index.2.2.2.1)).1,
        centered_effect_mem_trace_zero
          ((heisenberg ^ index.2.2.2.2)
            (effects index.1 index.2.1 index.2.2.1 index.2.2.2.1))⟩ :
        HermitianTraceZero (d := Fin d))
    let gramTerm := fun
        index : Nat.Primes × (Nat × (Context × (Outcome × Nat))) =>
      (precisionWeight index.1 index.2.1 * timeWeight index.2.2.2.2 *
          contextWeight index.2.2.1 index.2.2.2.1) •
        InnerProductSpace.rankOne ℝ (centered index) (centered index)
    Summable gramTerm →
      let gramian := ∑' index, gramTerm index
      inner ℝ D (gramian D) =
        ∑' index,
          precisionWeight index.1 index.2.1 * timeWeight index.2.2.2.2 *
            contextWeight index.2.2.1 index.2.2.2.1 *
              Complex.normSq (Matrix.trace (D.1 * (centered index).1)) := by
  dsimp only
  intro hsum
  let centered : Nat.Primes × (Nat × (Context × (Outcome × Nat))) →
      HermitianTraceZero (d := Fin d) := fun index =>
    ⟨centeredEffect
        ((heisenberg ^ index.2.2.2.2)
          (effects index.1 index.2.1 index.2.2.1 index.2.2.2.1)).1,
      centered_effect_mem_trace_zero
        ((heisenberg ^ index.2.2.2.2)
          (effects index.1 index.2.1 index.2.2.1 index.2.2.2.1))⟩
  let weight : Nat.Primes × (Nat × (Context × (Outcome × Nat))) → ℝ := fun index =>
    ((1 - primeEvidence s index.1) *
        (index.1.1 : ℝ) ^ (-s * ((index.2.1 + 1 : Nat) : ℝ)) /
          (∑' p : Nat.Primes, primeEvidence s p)) *
      ((1 - beta) * beta ^ index.2.2.2.2) *
        contextWeight index.2.2.1 index.2.2.2.1
  let term := fun index =>
    weight index • InnerProductSpace.rankOne ℝ (centered index) (centered index)
  change Summable term at hsum
  change inner ℝ D
      (((ContinuousLinearMap.apply ℝ (HermitianTraceZero (d := Fin d))) D)
        (∑' index, term index)) =
    ∑' index, weight index *
      Complex.normSq (Matrix.trace (D.1 * (centered index).1))
  have heval :=
    ((ContinuousLinearMap.apply ℝ (HermitianTraceZero (d := Fin d))) D).map_tsum hsum
  rw [heval]
  have happly := hsum.mapL
    ((ContinuousLinearMap.apply ℝ (HermitianTraceZero (d := Fin d))) D)
  have hinner := (innerSL ℝ D).map_tsum happly
  change (innerSL ℝ D)
      (∑' index,
        ((ContinuousLinearMap.apply ℝ (HermitianTraceZero (d := Fin d))) D)
          (term index)) = _
  rw [hinner]
  apply tsum_congr
  intro index
  have hnorm : Complex.normSq (Matrix.trace (D.1 * (centered index).1)) =
      (inner ℝ D (centered index)) ^ 2 := by
    rw [Complex.normSq_apply,
      trace_mul_im_zero D.1 (centered index).1 D.2.1 (centered index).2.1]
    rw [real_inner_eq_trace_mul]
    ring
  change inner ℝ D
      (((weight index) • InnerProductSpace.rankOne ℝ
        (centered index) (centered index)) D) = _
  rw [smul_apply, InnerProductSpace.rankOne_apply, inner_smul_right]
  rw [show inner ℝ (centered index) D = inner ℝ D (centered index) by
    exact real_inner_comm _ _]
  rw [inner_smul_right, hnorm]
  ring

#print axioms prime_time_gramian_energy_identity

end D5.S3.Observer.Linear.PrimeTimeGramianEnergyIdentity
