/- GID: D5/S3/Observer/Tomography/SequentialCompleteness
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/SequentialCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sequential readout completeness is equivalent to zero residual and full visible span. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

/- Library-search audit trail (2026-08-27):
   * Exact repository theorem `informational_completeness_four_way` supplies the same
     canonical density-state signature, scalar identity line, centered span, and
     orthogonal residual, with one additional centered-span clause. It is imported
     and projected to the three clauses named by this atom.
   * Searches across Observer and Quantum found no frozen theorem with exactly the
     source's three-clause sequential statement. The projection therefore preserves
     the source clauses while avoiding a duplicate proof of the canonical result.
   * Pinned Mathlib search found `List.TFAE.out`, which supplies both required
     pairwise equivalences. No new `def` or `abbrev` is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

namespace D5.S3.Observer.Tomography.SequentialCompleteness

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence

noncomputable section

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- Allowed sequential readouts are informationally complete exactly when their
visible Hermitian span is full, equivalently when its orthogonal residual is zero. -/
theorem sequential_completeness_criterion
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
      visible = ⊤] := by
  dsimp only
  have hFour := informational_completeness_four_way d centeredEffects
  dsimp only at hFour
  tfae_have 1 ↔ 2 := hFour.out 0 1
  tfae_have 2 ↔ 3 := hFour.out 1 2
  tfae_finish

#print axioms sequential_completeness_criterion

end

end D5.S3.Observer.Tomography.SequentialCompleteness
