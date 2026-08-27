/- GID: D5/S3/Quantum/PredictionDepth/FiniteInformationalEffectCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/FiniteInformationalEffectCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Informationally complete quantum effects admit a dimension-bounded finite certificate. -/

import D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/- Library-search audit trail (2026-08-27):
   * Exact family hits `centeredHermitianMap`, `traceZeroHermitian`,
     `trace_zero_hermitian_finrank`, and `informational_completeness_four_way`
     supply the canonical centered effect, exact real carrier, its dimension,
     and the density-state completeness bridge.
   * Exact pinned-Mathlib hit `Submodule.exists_fun_fin_finrank_span_eq`
     extracts a finite spanning subfamily and is applied directly.
   * `FinitePrimeTimeCertificate.finite_prime_time_certificate` is a close
     repository hit restricted to `Nat × Nat`; no existing theorem packages
     arbitrary-index effect selection, the dimension bound, full centered span,
     and separation by the original effects. -/

noncomputable section

open scoped ComplexOrder Matrix

namespace D5.S3.Quantum.PredictionDepth.FiniteInformationalEffectCertificate

open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.PredictionDepth.FiniteSequentialWordCertificate
open D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem centered_readout_eq_iff
    (d : Nat) [NeZero d]
    (rho sigma : DensityState (Fin d)) (effect : HermitianSpace d) :
    (Matrix.trace
        (CStarMatrix.ofMatrix.symm rho.1 *
          (centeredHermitianMap d effect).1.1)).re =
      (Matrix.trace
        (CStarMatrix.ofMatrix.symm sigma.1 *
          (centeredHermitianMap d effect).1.1)).re ↔
    (Matrix.trace
        (CStarMatrix.ofMatrix.symm rho.1 * effect.1)).re =
      (Matrix.trace
        (CStarMatrix.ofMatrix.symm sigma.1 * effect.1)).re := by
  have htraceRho : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 :=
    rho.2.2
  have htraceSigma : Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1) = 1 :=
    sigma.2.2
  have hcenteredDifference :
      Matrix.trace
          ((CStarMatrix.ofMatrix.symm rho.1 -
              CStarMatrix.ofMatrix.symm sigma.1) *
            centeredEffect effect.1) =
        Matrix.trace
          ((CStarMatrix.ofMatrix.symm rho.1 -
              CStarMatrix.ofMatrix.symm sigma.1) * effect.1) := by
    rw [centeredEffect, mul_sub, Matrix.trace_sub]
    have hzero :
        Matrix.trace
            (CStarMatrix.ofMatrix.symm rho.1 -
              CStarMatrix.ofMatrix.symm sigma.1) = 0 := by
      rw [Matrix.trace_sub, htraceRho, htraceSigma, sub_self]
    simp [hzero]
  have hrealDifference :
      (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 *
            (centeredHermitianMap d effect).1.1)).re -
          (Matrix.trace
            (CStarMatrix.ofMatrix.symm sigma.1 *
              (centeredHermitianMap d effect).1.1)).re =
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * effect.1)).re -
          (Matrix.trace
            (CStarMatrix.ofMatrix.symm sigma.1 * effect.1)).re := by
    rw [← Complex.sub_re, ← Complex.sub_re, ← Matrix.trace_sub,
      ← Matrix.trace_sub, ← sub_mul, ← sub_mul]
    change
      (Matrix.trace
          ((CStarMatrix.ofMatrix.symm rho.1 -
              CStarMatrix.ofMatrix.symm sigma.1) *
            centeredEffect effect.1)).re = _
    exact congrArg Complex.re hcenteredDifference
  constructor
  · intro h
    apply sub_eq_zero.mp
    rw [← hrealDifference]
    exact sub_eq_zero.mpr h
  · intro h
    apply sub_eq_zero.mp
    rw [hrealDifference]
    exact sub_eq_zero.mpr h

/-- An informationally complete family of quantum effects has a finite source
subfamily of at most `d^2 - 1` effects whose centered directions span the real
trace-zero Hermitian carrier and whose original probabilities still separate
all density states. -/
theorem finite_informational_effect_certificate
    (d : Nat) [NeZero d] {Index : Type*}
    (effects : Index ->
      {effect : HermitianSpace d //
        effect.1.PosSemidef ∧ (1 - effect.1).PosSemidef})
    (hcomplete : Function.Injective
      (fun rho : DensityState (Fin d) => fun i =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (effects i).1.1)).re)) :
    ∃ selected : Finset Index,
      selected.card ≤ d ^ 2 - 1 ∧
        Submodule.span ℝ
            (Set.range fun i : selected =>
              centeredHermitianMap d (effects i.1).1) = ⊤ ∧
        Function.Injective
          (fun rho : DensityState (Fin d) => fun i : selected =>
            (Matrix.trace
              (CStarMatrix.ofMatrix.symm rho.1 * (effects i.1).1.1)).re) := by
  classical
  let centeredEffects := fun i : Index =>
    centeredHermitianMap d (effects i).1
  have hcenteredComplete : Function.Injective
      (fun rho : DensityState (Fin d) => fun i =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 * (centeredEffects i).1.1)).re) := by
    intro rho sigma hreadout
    apply hcomplete
    funext i
    exact (centered_readout_eq_iff d rho sigma (effects i).1).mp
      (congrFun hreadout i)
  have hcompleteSpan :
      Submodule.span ℝ (Set.range centeredEffects) = ⊤ :=
    ((informational_completeness_four_way d centeredEffects).out 0 3).mp
      hcenteredComplete
  obtain ⟨basisEffects, hbasisMem, hbasisSpan, _hbasisIndependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range centeredEffects)
  choose chosen hchosen using hbasisMem
  let selected : Finset Index := Finset.univ.image chosen
  have hselectedSpan :
      Submodule.span ℝ
          (Set.range fun i : selected => centeredEffects i.1) = ⊤ := by
    apply top_unique
    rw [← hcompleteSpan, ← hbasisSpan]
    apply Submodule.span_mono
    rintro value ⟨i, rfl⟩
    exact
      (show basisEffects i ∈
          Set.range (fun index : selected => centeredEffects index.1) from
        ⟨⟨chosen i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩,
          hchosen i⟩)
  have hselectedCard : selected.card ≤ d ^ 2 - 1 := by
    calc
      selected.card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℝ
          (Submodule.span ℝ (Set.range centeredEffects)) := by simp
      _ = Module.finrank ℝ (traceZeroHermitian d) := by
        rw [hcompleteSpan, finrank_top]
      _ = d ^ 2 - 1 := trace_zero_hermitian_finrank d
  have hselectedCenteredComplete : Function.Injective
      (fun rho : DensityState (Fin d) => fun i : selected =>
        (Matrix.trace
          (CStarMatrix.ofMatrix.symm rho.1 *
            (centeredEffects i.1).1.1)).re) :=
    ((informational_completeness_four_way d
      (fun i : selected => centeredEffects i.1)).out 3 0).mp hselectedSpan
  refine ⟨selected, hselectedCard, hselectedSpan, ?_⟩
  intro rho sigma hreadout
  apply hselectedCenteredComplete
  funext i
  exact (centered_readout_eq_iff d rho sigma (effects i.1).1).mpr
    (congrFun hreadout i)

#print axioms finite_informational_effect_certificate

end D5.S3.Quantum.PredictionDepth.FiniteInformationalEffectCertificate
