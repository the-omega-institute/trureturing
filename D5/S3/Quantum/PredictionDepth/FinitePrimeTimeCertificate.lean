/- GID: D5/S3/Quantum/PredictionDepth/FinitePrimeTimeCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/PredictionDepth/FinitePrimeTimeCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete natural-indexed quantum effects have a finite dimension-bounded certificate. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
import D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/- Library-search audit trail (2026-08-27):
   * Exact family hit HermitianTraceZero supplies the real traceless Hermitian carrier.
   * Exact repository hit trace_zero_hermitian_finrank supplies the dimension d^2 - 1 after a
     local linear equivalence between the two canonical nested-subtype presentations.
   * Exact pinned-Mathlib hit Submodule.exists_fun_fin_finrank_span_eq extracts a finite
     linearly independent subfamily from a spanning range and is applied directly.
   * Repository searches found no theorem packaging the selected natural index-time pairs,
     their dimension bound, spanning, and state-separation conclusion. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

namespace D5.S3.Quantum.PredictionDepth.FinitePrimeTimeCertificate

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

private theorem trace_zero_inner_eq_trace
    {d : Nat} (A B : HermitianTraceZero (d := Fin d)) :
    inner ℝ A B = (Matrix.trace (A.1 * B.1)).re := by
  change (Matrix.trace (B.1 * 1 * (A.1)ᴴ)).re = _
  rw [Matrix.mul_one, A.2.1.eq, Matrix.trace_mul_comm]

/-- If every natural-indexed, finite-time effect spans the real traceless Hermitian carrier,
a finite set of concrete index-time pairs of size at most d^2 - 1 already spans it and
therefore separates every pair of density states. -/
theorem finite_prime_time_certificate
    (d : Nat) [NeZero d]
    (effects : Nat × Nat -> HermitianTraceZero (d := Fin d))
    (hcomplete : Submodule.span ℝ (Set.range effects) = ⊤) :
    ∃ selected : Finset (Nat × Nat),
      selected.card ≤ d ^ 2 - 1 ∧
        Submodule.span ℝ
            (Set.range fun index : selected => effects index.1) = ⊤ ∧
        ∀ rho sigma : DensityState (Fin d),
          (∀ index : selected,
            (Matrix.trace
                (CStarMatrix.ofMatrix.symm rho.1 * (effects index.1).1)).re =
              (Matrix.trace
                (CStarMatrix.ofMatrix.symm sigma.1 * (effects index.1).1)).re) ->
          rho = sigma := by
  classical
  let carrier := HermitianTraceZero (d := Fin d)
  let directEquiv : carrier ≃ₗ[ℝ] traceZeroHermitian d :=
    { toFun := fun X => ⟨⟨X.1, X.2.1⟩, X.2.2⟩
      invFun := fun X => ⟨X.1.1, X.1.2, X.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdimension :
      Module.finrank ℝ (HermitianTraceZero (d := Fin d)) = d ^ 2 - 1 := by
    change Module.finrank ℝ carrier = d ^ 2 - 1
    rw [directEquiv.finrank_eq]
    exact trace_zero_hermitian_finrank d
  obtain ⟨basisEffects, hbasisMem, hbasisSpan, _hbasisIndependent⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range effects)
  choose chosen hchosen using hbasisMem
  let selected : Finset (Nat × Nat) := Finset.univ.image chosen
  have hselectedSpan :
      Submodule.span ℝ
          (Set.range fun index : selected => effects index.1) = ⊤ := by
    apply top_unique
    rw [← hcomplete, ← hbasisSpan]
    apply Submodule.span_mono
    rintro value ⟨i, rfl⟩
    exact
      (show basisEffects i ∈
          Set.range (fun index : selected => effects index.1) from
        ⟨⟨chosen i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩,
          hchosen i⟩)
  have hcoordinateSeparation :
      ∀ X Y : HermitianTraceZero (d := Fin d),
        (∀ index : selected,
          inner ℝ X (effects index.1) = inner ℝ Y (effects index.1)) ->
        X = Y := by
    intro X Y hreadout
    have hallReadout :
        ∀ Z : HermitianTraceZero (d := Fin d), inner ℝ X Z = inner ℝ Y Z := by
      intro Z
      have hZ :
          Z ∈ Submodule.span ℝ
            (Set.range fun index : selected => effects index.1) := by
        rw [hselectedSpan]
        exact Submodule.mem_top
      induction hZ using Submodule.span_induction with
      | mem Z hgenerator =>
          rcases hgenerator with ⟨index, rfl⟩
          exact hreadout index
      | zero => simp
      | add first second _ _ hfirst hsecond =>
          simp only [inner_add_right, hfirst, hsecond]
      | smul scalar Z _ hZ =>
          simp only [real_inner_smul_right, hZ]
    have hzero : inner ℝ (X - Y) (X - Y) = 0 := by
      rw [inner_sub_left, sub_eq_zero]
      exact hallReadout (X - Y)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  refine ⟨selected, ?_, hselectedSpan, ?_⟩
  · calc
      selected.card ≤ Finset.univ.card := Finset.card_image_le
      _ = Module.finrank ℝ (Submodule.span ℝ (Set.range effects)) := by
        simp
      _ = Module.finrank ℝ (HermitianTraceZero (d := Fin d)) := by
        rw [hcomplete, finrank_top]
      _ = d ^ 2 - 1 := hdimension
  · intro rho sigma hreadout
    let D : HermitianTraceZero (d := Fin d) :=
      ⟨CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1,
        by
          have hrho : (CStarMatrix.ofMatrix.symm rho.1).IsHermitian :=
            congrArg CStarMatrix.ofMatrix.symm rho.2.1.isSelfAdjoint.star_eq
          have hsigma : (CStarMatrix.ofMatrix.symm sigma.1).IsHermitian :=
            congrArg CStarMatrix.ofMatrix.symm sigma.2.1.isSelfAdjoint.star_eq
          exact hrho.sub hsigma,
        by
          have hrhoTrace : Matrix.trace (CStarMatrix.ofMatrix.symm rho.1) = 1 :=
            rho.2.2
          have hsigmaTrace : Matrix.trace (CStarMatrix.ofMatrix.symm sigma.1) = 1 :=
            sigma.2.2
          rw [Matrix.trace_sub, hrhoTrace, hsigmaTrace, sub_self]⟩
    have hDreadout :
        ∀ index : selected,
          inner ℝ D (effects index.1) =
            inner ℝ (0 : HermitianTraceZero (d := Fin d)) (effects index.1) := by
      intro index
      rw [trace_zero_inner_eq_trace, trace_zero_inner_eq_trace]
      simp only [Submodule.coe_zero, zero_mul, Matrix.trace_zero, Complex.zero_re]
      dsimp only [D]
      rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, sub_eq_zero]
      exact hreadout index
    have hDzero := hcoordinateSeparation D 0 hDreadout
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    have hvalue := congrArg
      (fun Z : HermitianTraceZero (d := Fin d) => Z.1) hDzero
    simpa only [D, Submodule.coe_zero, sub_eq_zero] using hvalue

#print axioms finite_prime_time_certificate

end D5.S3.Quantum.PredictionDepth.FinitePrimeTimeCertificate
