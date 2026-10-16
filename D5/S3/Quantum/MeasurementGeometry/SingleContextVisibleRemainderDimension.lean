/- GID: D5/S3/Quantum/MeasurementGeometry/SingleContextVisibleRemainderDimension
   generality: G
   mirror-B: D5/B/S3/Quantum/MeasurementGeometry/SingleContextVisibleRemainderDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One rank-one context exposes one diagonal slice and leaves its orthogonal remainder. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Tomography.OneStepProbabilityInnovation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.MeasurementGeometry.SingleContextVisibleRemainderDimension

open D5.S3.Observer.Conditioning
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Quantum.Tomography.OneStepProbabilityInnovation
open D5.S3.Quantum.Tomography.RankOneContextCommutator

local instance matrixNormedAddCommGroup (d : Nat) :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace (d : Nat) :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace (d : Nat) :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- The linearized probability vector from source lines 13513-13515, restricted to
trace-zero state directions. -/
noncomputable def contextProbabilityDirection {d : Nat} (B : RankOneContext d) :
    traceZeroHermitian d →ₗ[ℝ] (Fin d → ℝ) where
  toFun A j := contextProbability A.1.1 B j
  map_add' A C := by
    funext j
    simp [contextProbability, Matrix.add_mul, Matrix.trace_add]
  map_smul' r A := by
    funext j
    simp [contextProbability, Matrix.trace_smul, Complex.mul_re]

/-- The source's visible linear-dimension ratio (lines 13546-13553). -/
noncomputable def visibleRatio {d : Nat} (B : RankOneContext d) : ℚ :=
  (Module.finrank ℝ (diagonalTraceZeroSubspace B) : ℚ) /
    (Module.finrank ℝ (traceZeroHermitian d) : ℚ)

/-- The source's orthogonal-remainder linear-dimension ratio (lines 13556-13563). -/
noncomputable def remainderRatio {d : Nat} (B : RankOneContext d) : ℚ :=
  (Module.finrank ℝ ((diagonalTraceZeroSubspace B)ᗮ) : ℚ) /
    (Module.finrank ℝ (traceZeroHermitian d) : ℚ)

/-- The fraction of trace-zero state directions exposed by the actual probability-vector
readout (lines 13568-13573). -/
noncomputable def probabilityVectorExposedRatio {d : Nat} (B : RankOneContext d) : ℚ :=
  (Module.finrank ℝ (LinearMap.range (contextProbabilityDirection B)) : ℚ) /
    (Module.finrank ℝ (traceZeroHermitian d) : ℚ)

private theorem hermitian_trace_eq_real {d : Nat} (A : HermitianSpace d) :
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

private theorem projector_trace_mul_real {d : Nat} (B : RankOneContext d)
    (A : HermitianSpace d) (j : Fin d) :
    Matrix.trace (B.projector j * A.1) =
      ((Matrix.trace (B.projector j * A.1)).re : ℂ) := by
  have hAstar := A.2
  change star A.1 = A.1 at hAstar
  have hA : A.1ᴴ = A.1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hAstar
  have hstar : star (Matrix.trace (B.projector j * A.1)) =
      Matrix.trace (B.projector j * A.1) := by
    calc
      star (Matrix.trace (B.projector j * A.1)) =
          Matrix.trace ((B.projector j * A.1)ᴴ) :=
        (Matrix.trace_conjTranspose _).symm
      _ = Matrix.trace (A.1 * B.projector j) := by
        rw [Matrix.conjTranspose_mul, hA, (B.rankOne j).1]
      _ = Matrix.trace (B.projector j * A.1) := Matrix.trace_mul_comm _ _
  exact (Complex.conj_eq_iff_re.mp hstar).symm

private theorem basisProjector_linearIndependent {d : Nat} (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    LinearIndependent ℝ (basisProjector B) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficient hsum j
  have hmatrix : ∑ i, coefficient i • B.projector i = 0 := by
    have hvalues := congrArg (fun A : HermitianSpace d => A.1) hsum
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      basisProjector_val] using hvalues
  have htrace :
      ∑ i, coefficient i • Matrix.trace (B.projector j * B.projector i) = 0 := by
    have hvalues := congrArg
      (fun X : Matrix (Fin d) (Fin d) ℂ => Matrix.trace (B.projector j * X)) hmatrix
    simpa only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
      Matrix.mul_zero, Matrix.trace_zero] using hvalues
  have hcoefficient : (coefficient j : ℂ) = 0 := by
    calc
      (coefficient j : ℂ) =
          ∑ i, coefficient i • Matrix.trace (B.projector j * B.projector i) := by
        rw [Finset.sum_eq_single j]
        · rw [hB.idempotent j, (B.rankOne j).2.2.1]
          simp
        · intro i _ hij
          rw [hB.orthogonal j i (Ne.symm hij)]
          simp
        · simp
      _ = 0 := htrace
  exact_mod_cast hcoefficient

private theorem diagonal_subspace_finrank {d : Nat} (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    Module.finrank ℝ (diagonalSubspace B) = d := by
  rw [diagonalSubspace, finrank_span_eq_card (basisProjector_linearIndependent B hB),
    Fintype.card_fin]

private noncomputable def diagonalRealTrace {d : Nat} (B : RankOneContext d) :
    diagonalSubspace B →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace A.1.1).re
  map_add' A C := by simp [Matrix.trace_add]
  map_smul' r A := by simp [Matrix.trace_smul, Complex.mul_re]

private noncomputable def diagonalTraceZeroEquiv {d : Nat} (B : RankOneContext d) :
    diagonalTraceZeroSubspace B ≃ₗ[ℝ] LinearMap.ker (diagonalRealTrace B) where
  toFun A := ⟨⟨A.1.1, A.2⟩, by
    change (Matrix.trace A.1.1.1).re = 0
    simpa using congrArg Complex.re A.1.2⟩
  invFun A := by
    have hreal : (Matrix.trace A.1.1.1).re = 0 := by
      simpa [diagonalRealTrace] using A.2
    have htrace : Matrix.trace A.1.1.1 = 0 := by
      rw [hermitian_trace_eq_real A.1.1, hreal]
      rfl
    exact ⟨⟨A.1.1, htrace⟩, A.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem diagonal_real_trace_surjective {d : Nat} (hd : 1 ≤ d)
    (B : RankOneContext d) : Function.Surjective (diagonalRealTrace B) := by
  classical
  intro r
  let j : Fin d := ⟨0, Nat.zero_lt_of_lt hd⟩
  let P : diagonalSubspace B :=
    ⟨basisProjector B j, Submodule.subset_span ⟨j, rfl⟩⟩
  refine ⟨r • P, ?_⟩
  simp [diagonalRealTrace, P, basisProjector_val, (B.rankOne j).2.2.1]

private theorem diagonal_trace_zero_finrank {d : Nat} (hd : 1 ≤ d)
    (B : RankOneContext d) (hB : IsRecordMeasurement B.projector) :
    Module.finrank ℝ (diagonalTraceZeroSubspace B) = d - 1 := by
  have hrange : LinearMap.range (diagonalRealTrace B) = ⊤ :=
    LinearMap.range_eq_top.mpr (diagonal_real_trace_surjective hd B)
  have hrankNullity := (diagonalRealTrace B).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self, diagonal_subspace_finrank B hB] at hrankNullity
  calc
    Module.finrank ℝ (diagonalTraceZeroSubspace B) =
        Module.finrank ℝ (LinearMap.ker (diagonalRealTrace B)) :=
      (diagonalTraceZeroEquiv B).finrank_eq
    _ = d - 1 := by omega

private theorem trace_zero_basis_measurement_eq_probability_sum {d : Nat}
    (B : RankOneContext d) (hB : IsRecordMeasurement B.projector)
    (A : traceZeroHermitian d) :
    (traceZeroBasisMeasurement B hB A).1 =
      ∑ j, contextProbabilityDirection B A j • basisProjector B j := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, basisProjector_val]
  change unreadState B.projector A.1.1 =
    ∑ j, (contextProbabilityDirection B A j : ℂ) • B.projector j
  rw [unreadState]
  apply Finset.sum_congr rfl
  intro j _
  rw [(B.rankOne j).2.2.2 A.1.1, projector_trace_mul_real B A.1 j]
  change ((Matrix.trace (B.projector j * A.1.1)).re : ℂ) • B.projector j =
    ((Matrix.trace (A.1.1 * B.projector j)).re : ℂ) • B.projector j
  rw [Matrix.trace_mul_comm]

private theorem probability_direction_ker_eq_measurement_ker {d : Nat}
    (B : RankOneContext d) (hB : IsRecordMeasurement B.projector) :
    LinearMap.ker (contextProbabilityDirection B) =
      LinearMap.ker (traceZeroBasisMeasurement B hB) := by
  classical
  ext A
  constructor
  · intro hProbability
    change contextProbabilityDirection B A = 0 at hProbability
    change traceZeroBasisMeasurement B hB A = 0
    apply Subtype.ext
    rw [trace_zero_basis_measurement_eq_probability_sum B hB A]
    have hcoordinate (j : Fin d) : contextProbabilityDirection B A j = 0 :=
      by simpa using congrFun hProbability j
    simp [hcoordinate]
  · intro hMeasurement
    change traceZeroBasisMeasurement B hB A = 0 at hMeasurement
    change contextProbabilityDirection B A = 0
    apply funext
    intro j
    have hsum :
        ∑ j, contextProbabilityDirection B A j • basisProjector B j = 0 := by
      rw [← trace_zero_basis_measurement_eq_probability_sum B hB A]
      exact congrArg Subtype.val hMeasurement
    exact Fintype.linearIndependent_iff.mp (basisProjector_linearIndependent B hB)
      (contextProbabilityDirection B A) hsum j

private theorem probability_direction_range_finrank {d : Nat} (hd : 1 ≤ d)
    (B : RankOneContext d) (hB : IsRecordMeasurement B.projector) :
    Module.finrank ℝ (LinearMap.range (contextProbabilityDirection B)) = d - 1 := by
  have hmeasurementRange :
      Module.finrank ℝ (LinearMap.range (traceZeroBasisMeasurement B hB)) = d - 1 := by
    rw [(trace_zero_basis_measurement_is_orthogonal_projection B hB).2,
      diagonal_trace_zero_finrank hd B hB]
  have hProbability := (contextProbabilityDirection B).finrank_range_add_finrank_ker
  have hMeasurement := (traceZeroBasisMeasurement B hB).finrank_range_add_finrank_ker
  rw [probability_direction_ker_eq_measurement_ker B hB] at hProbability
  rw [hmeasurementRange] at hMeasurement
  omega

/-- A single rank-one PVM exposes at most `d - 1` trace-zero state directions, leaves the
orthogonal `d^2 - d` remainder, and has the two source dimension ratios. The final leaf uses
the actual probability-vector readout range rather than a state-probability mass. -/
theorem single_context_visible_remainder_dimension
    (d : Nat) (hd : 2 ≤ d) (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    Module.finrank ℝ (diagonalTraceZeroSubspace B) ≤ d - 1 ∧
      Module.finrank ℝ ((diagonalTraceZeroSubspace B)ᗮ) = d ^ 2 - d ∧
      visibleRatio B = ((d - 1 : Nat) : ℚ) / ((d ^ 2 - 1 : Nat) : ℚ) ∧
      visibleRatio B = 1 / ((d + 1 : Nat) : ℚ) ∧
      remainderRatio B = ((d ^ 2 - d : Nat) : ℚ) / ((d ^ 2 - 1 : Nat) : ℚ) ∧
      remainderRatio B = (d : ℚ) / ((d + 1 : Nat) : ℚ) ∧
      probabilityVectorExposedRatio B = 1 / ((d + 1 : Nat) : ℚ) := by
  letI : NeZero d := ⟨by omega⟩
  have hdOne : 1 ≤ d := le_trans (by omega) hd
  have hdStrict : 1 < d := lt_of_lt_of_le (by omega) hd
  have hvisible : Module.finrank ℝ (diagonalTraceZeroSubspace B) = d - 1 :=
    diagonal_trace_zero_finrank hdOne B hB
  have hambient : Module.finrank ℝ (traceZeroHermitian d) = d ^ 2 - 1 :=
    trace_zero_hermitian_finrank d
  have hdimensionSum := (diagonalTraceZeroSubspace B).finrank_add_finrank_orthogonal
  have hremainder : Module.finrank ℝ ((diagonalTraceZeroSubspace B)ᗮ) = d ^ 2 - d := by
    rw [hvisible, hambient] at hdimensionSum
    omega
  have hprobability :
      Module.finrank ℝ (LinearMap.range (contextProbabilityDirection B)) = d - 1 :=
    probability_direction_range_finrank hdOne B hB
  have hdQ : (1 : ℚ) < (d : ℚ) := by exact_mod_cast hdStrict
  have hpowOne : 1 ≤ d ^ 2 := by nlinarith
  have hdPow : d ≤ d ^ 2 := by nlinarith
  have hdenominator : (d : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hsuccessor : (d : ℚ) + 1 ≠ 0 := by nlinarith
  refine ⟨hvisible.le, hremainder, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [visibleRatio, hvisible, hambient]
  · simp only [visibleRatio, hvisible, hambient]
    push_cast [Nat.cast_sub hdOne, Nat.cast_sub hpowOne]
    field_simp [hdenominator, hsuccessor]
    ring
  · simp only [remainderRatio, hremainder, hambient]
  · simp only [remainderRatio, hremainder, hambient]
    push_cast [Nat.cast_sub hdPow, Nat.cast_sub hpowOne]
    field_simp [hdenominator, hsuccessor]
    ring
  · simp only [probabilityVectorExposedRatio, hprobability, hambient]
    push_cast [Nat.cast_sub hdOne, Nat.cast_sub hpowOne]
    field_simp [hdenominator, hsuccessor]
    ring

/-- Reverse probe for source assertions A1 and A2: in dimension two, the visible slice is
strictly smaller than its orthogonal remainder. -/
example (B : RankOneContext 2) (hB : IsRecordMeasurement B.projector) :
    Module.finrank ℝ (diagonalTraceZeroSubspace B) <
      Module.finrank ℝ ((diagonalTraceZeroSubspace B)ᗮ) := by
  have h := single_context_visible_remainder_dimension 2 (by omega) B hB
  omega

/-- Reverse probe for source assertion A7: the actual probability-vector range exposes a
strictly subunit fraction once `d >= 2`. -/
example (d : Nat) (hd : 2 ≤ d) (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    probabilityVectorExposedRatio B < 1 := by
  have h := single_context_visible_remainder_dimension d hd B hB
  rw [h.2.2.2.2.2.2]
  have hden : (1 : ℚ) < ((d + 1 : Nat) : ℚ) := by
    exact_mod_cast (show 1 < d + 1 by omega)
  simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℚ) < 1) hden

/-- Trivialization probe for source assertion A4: at the excluded value `d = 1`, its
`1 / (d + 1)` conclusion is false even for a rank-one PVM. -/
example (B : RankOneContext 1) (hB : IsRecordMeasurement B.projector) :
    visibleRatio B ≠ 1 / (((1 : Nat) + 1 : Nat) : ℚ) := by
  have hvisible := diagonal_trace_zero_finrank (d := 1) (by omega) B hB
  have hambient := trace_zero_hermitian_finrank 1
  simp [visibleRatio, hvisible, hambient]

#print axioms single_context_visible_remainder_dimension

end D5.S3.Quantum.MeasurementGeometry.SingleContextVisibleRemainderDimension
