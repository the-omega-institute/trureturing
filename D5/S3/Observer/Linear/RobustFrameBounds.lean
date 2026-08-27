/- GID: D5/S3/Observer/Linear/RobustFrameBounds
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/RobustFrameBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Weighted readouts satisfy sharp frame bounds and spectral conditioning. -/

import D5.S3.Quantum.Tomography.InformationalCompletenessEquivalence
import Mathlib.Analysis.InnerProductSpace.SingularValues

/- Library-search audit trail (2026-08-27):
   * Exact repository hits `traceZeroHermitian` and
     `trace_zero_hermitian_finrank` supply the source's real traceless
     Hermitian carrier and its dimension.
   * Exact pinned-Mathlib component hits `LinearMap.singularValues`,
     `LinearMap.sq_singularValues_fin`,
     `LinearMap.injective_iff_forall_lt_finrank_singularValues_pos`, and the
     ordered eigenbasis of `LinearMap.isSymmetric_adjoint_comp_self` supply
     the Gram spectral bounds and completeness criterion.
   * Repository and pinned-Mathlib searches found no exact theorem packaging
     both frame bounds, completeness, and the condition-number identity on
     the source carrier. -/

namespace D5.S3.Observer.Linear.RobustFrameBounds

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open InnerProductSpace Module
open scoped RealInnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

private theorem linear_map_sharp_frame_bounds
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (analysis : E →ₗ[ℝ] F) (n : ℕ)
    (hn : finrank ℝ E = n + 1) :
    let alpha :=
      analysis.isSymmetric_adjoint_comp_self.eigenvalues hn (Fin.last n)
    let beta :=
      analysis.isSymmetric_adjoint_comp_self.eigenvalues hn (0 : Fin (n + 1))
    let conditionNumber :=
      analysis.singularValues 0 / analysis.singularValues n
    (∀ x : E,
      alpha * ‖x‖ ^ 2 ≤ ‖analysis x‖ ^ 2 ∧
        ‖analysis x‖ ^ 2 ≤ beta * ‖x‖ ^ 2) ∧
    (Function.Injective analysis ↔ 0 < alpha) ∧
    conditionNumber = Real.sqrt (beta / alpha) := by
  dsimp only
  let gram := analysis.adjoint.comp analysis
  let hgram := analysis.isSymmetric_adjoint_comp_self
  let eigenbasis := hgram.eigenvectorBasis hn
  have henergy (x : E) :
      ‖analysis x‖ ^ 2 =
        ∑ i : Fin (n + 1),
          hgram.eigenvalues hn i * (inner ℝ (eigenbasis i) x) ^ 2 := by
    calc
      ‖analysis x‖ ^ 2 = inner ℝ (analysis x) (analysis x) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (gram x) x := by
        simpa [gram, LinearMap.comp_apply] using
          (analysis.adjoint_inner_left x (analysis x)).symm
      _ = ∑ i : Fin (n + 1),
          inner ℝ (gram x) (eigenbasis i) * inner ℝ (eigenbasis i) x := by
        exact (eigenbasis.sum_inner_mul_inner (gram x) x).symm
      _ = ∑ i : Fin (n + 1),
          hgram.eigenvalues hn i * (inner ℝ (eigenbasis i) x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hgram x (eigenbasis i), hgram.apply_eigenvectorBasis hn]
        simp only [eigenbasis, real_inner_smul_right, real_inner_comm,
          RCLike.ofReal_real_eq_id, id_eq, pow_two]
        ring
  have halpha :
      analysis.singularValues n ^ 2 =
        hgram.eigenvalues hn (Fin.last n) := by
    simpa [hgram] using
      analysis.sq_singularValues_fin hn (Fin.last n)
  have hbeta :
      analysis.singularValues 0 ^ 2 =
        hgram.eigenvalues hn (0 : Fin (n + 1)) := by
    simpa [hgram] using
      analysis.sq_singularValues_fin hn (0 : Fin (n + 1))
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · rw [henergy]
      rw [← eigenbasis.sum_sq_inner_right x, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · exact hgram.eigenvalues_antitone hn (Fin.le_last i)
      · positivity
    · rw [henergy]
      rw [← eigenbasis.sum_sq_inner_right x, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · exact hgram.eigenvalues_antitone hn (Fin.zero_le i)
      · positivity
  · rw [analysis.injective_iff_forall_lt_finrank_singularValues_pos, hn]
    constructor
    · intro hall
      have hlast := hall n (Nat.lt_succ_self n)
      rw [← halpha]
      positivity
    · intro halphaPositive i hi
      have hlast : 0 < analysis.singularValues n := by
        rw [← halpha] at halphaPositive
        nlinarith [analysis.singularValues_nonneg n]
      have hin : i ≤ n := Nat.lt_succ_iff.mp hi
      exact hlast.trans_le (analysis.singularValues_antitone hin)
  · rw [← hbeta, ← halpha, ← div_pow]
    exact (Real.sqrt_sq (div_nonneg
      (analysis.singularValues_nonneg 0)
      (analysis.singularValues_nonneg n))).symm

private theorem trace_zero_finrank_as_succ
    (d : ℕ) [NeZero d] (hd : 1 < d) :
    finrank ℝ (traceZeroHermitian d) = (d ^ 2 - 2) + 1 := by
  rw [trace_zero_hermitian_finrank d]
  have hsq : 2 ≤ d ^ 2 := by
    nlinarith
  omega

/-- Finite weighted readouts on the traceless Hermitian carrier satisfy the
sharp Gram frame bounds. Their analysis map is injective exactly when the
least Gram eigenvalue is positive, and the singular-value condition number is
the square root of the Gram eigenvalue ratio. The dimension hypothesis excludes
the zero-dimensional traceless carrier at `d = 1`, where a least eigenvalue is
not defined by the source construction. -/
theorem robust_observer_frame_bounds
    (d : ℕ) [NeZero d] (hd : 1 < d)
    {Index : Type*} [Fintype Index]
    (weights : Index → NNReal)
    (effects : Index → HermitianSpace d) :
    let analysis :
        traceZeroHermitian d →ₗ[ℝ] EuclideanSpace ℝ Index :=
      { toFun := fun D => WithLp.toLp 2 fun i =>
          Real.sqrt (weights i : ℝ) * inner ℝ D.1 (effects i)
        map_add' := by
          intro D₁ D₂
          ext i
          simp [inner_add_left, mul_add]
        map_smul' := by
          intro c D
          ext i
          change Real.sqrt (weights i : ℝ) *
              inner ℝ (c • D.1) (effects i) =
            c * (Real.sqrt (weights i : ℝ) *
              inner ℝ D.1 (effects i))
          rw [real_inner_smul_left]
          ring }
    let alpha :=
      analysis.isSymmetric_adjoint_comp_self.eigenvalues
        (trace_zero_finrank_as_succ d hd)
        (Fin.last (d ^ 2 - 2))
    let beta :=
      analysis.isSymmetric_adjoint_comp_self.eigenvalues
        (trace_zero_finrank_as_succ d hd)
        (0 : Fin (d ^ 2 - 2 + 1))
    let conditionNumber :=
      analysis.singularValues 0 /
        analysis.singularValues (d ^ 2 - 2)
    (∀ D : traceZeroHermitian d,
      alpha * ‖D‖ ^ 2 ≤ ‖analysis D‖ ^ 2 ∧
        ‖analysis D‖ ^ 2 ≤ beta * ‖D‖ ^ 2) ∧
    (Function.Injective analysis ↔ 0 < alpha) ∧
    conditionNumber = Real.sqrt (beta / alpha) := by
  dsimp only
  apply linear_map_sharp_frame_bounds
    (n := d ^ 2 - 2)

#print axioms robust_observer_frame_bounds

end D5.S3.Observer.Linear.RobustFrameBounds
