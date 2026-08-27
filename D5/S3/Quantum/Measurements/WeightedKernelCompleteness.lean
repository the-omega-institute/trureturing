/- GID: D5/S3/Quantum/Measurements/WeightedKernelCompleteness
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/WeightedKernelCompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive weighted effect quadratics have exactly the common trace-effect kernel. -/

import D5.S3.Quantum.Measurement.OperationalObservationKernel

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

namespace D5.S3.Quantum.Measurements.WeightedKernelCompleteness

open D5.S3.Quantum.Measurement.BasisMeasurementProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {d : Nat}

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

def weightedGramian {Index : Type*} [Fintype Index]
    (effects : Index → traceZeroHermitian d) (weight : Index → Real)
    (D : traceZeroHermitian d) : Real :=
  ∑ i, weight i * (inner ℝ D (effects i)) ^ 2

theorem weighted_kernel_completeness
    {Index : Type*} [Fintype Index]
    (effects : Index → traceZeroHermitian d)
    (weight : Index → Real) (hpositive : ∀ i, 0 < weight i) :
      {D | weightedGramian effects weight D = 0} =
        {D | ∀ i, inner ℝ D (effects i) = 0} ∧
      ((∀ D, D ≠ 0 → 0 < weightedGramian effects weight D) ↔
        Function.Injective (fun D => fun i => inner ℝ D (effects i))) := by
  have hkernel : {D | weightedGramian effects weight D = 0} =
      {D | ∀ i, inner ℝ D (effects i) = 0} := by
    ext D
    constructor
    · intro hzero i
      have hterm : weight i * (inner ℝ D (effects i)) ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          mul_nonneg (le_of_lt (hpositive j)) (sq_nonneg _))).mp
            hzero i (Finset.mem_univ i)
      have hsq : (inner ℝ D (effects i)) ^ 2 = 0 :=
        (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hpositive i))
      exact sq_eq_zero_iff.mp hsq
    · intro hzero
      unfold weightedGramian
      apply Finset.sum_eq_zero
      intro i hi
      simp [hzero i]
  constructor
  · exact hkernel
  · constructor
    · intro hpositive X Y hreadout
      have hzero : weightedGramian effects weight (X - Y) = 0 := by
        unfold weightedGramian
        apply Finset.sum_eq_zero
        intro i hi
        have hi' := congrFun hreadout i
        change inner ℝ X (effects i) = inner ℝ Y (effects i) at hi'
        rw [inner_sub_left]
        rw [sub_eq_zero.mpr hi']
        simp
      by_contra hne
      have hstrict := hpositive (X - Y) (sub_ne_zero.mpr hne)
      exact (ne_of_gt hstrict) hzero
    · intro hinjective D hD
      have hnotall : ¬ (∀ i, inner ℝ D (effects i) = 0) := by
        intro hall
        have hreadout :
            (fun i => inner ℝ D (effects i)) =
              (fun i => inner ℝ (0 : traceZeroHermitian d) (effects i)) := by
          funext i
          simp [hall i]
        have hDzero := hinjective hreadout
        exact hD hDzero
      have hsome : ∃ i, inner ℝ D (effects i) ≠ 0 := by
        by_contra hnone
        apply hnotall
        intro i
        by_contra hi
        exact hnone ⟨i, hi⟩
      unfold weightedGramian
      apply Finset.sum_pos'
      · intro i hi
        exact mul_nonneg (le_of_lt (hpositive i)) (sq_nonneg _)
      · rcases hsome with ⟨i, hi⟩
        exact ⟨i, Finset.mem_univ i,
          mul_pos (hpositive i) (sq_pos_of_ne_zero hi)⟩

#print axioms weighted_kernel_completeness

end D5.S3.Quantum.Measurements.WeightedKernelCompleteness
