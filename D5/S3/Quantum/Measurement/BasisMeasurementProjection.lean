/- GID: D5/S3/Quantum/Measurement/BasisMeasurementProjection
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/BasisMeasurementProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Basis dephasing is the orthogonal projection onto diagonal Hermitian matrices. -/

import D5.S3.Observer.Conditioning.UnreadStateOrthogonalProjection
import D5.S3.Quantum.Tomography.RankOneContextCommutator
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'basis_measurement_is_orthogonal_projection' D5 Golden/Frozen/accepted`
     returned no matches.
   * Public repository hits `Conditioning.unreadState_trace`,
     `Conditioning.unreadState_idempotent`, and
     `UnreadStateOrthogonalProjection.unread_state_orthogonal_projection` supply trace
     preservation and the arbitrary finite-PVM projection laws. The latter has no Hermitian
     real-linear restriction, rank-one diagonal range, trace-zero restriction, or witness.
   * Private repository hits include `unreadState_hilbert_schmidt_self_adjoint`,
     `dephasing_eq_sum_trace_smul`, `unread_projector`, and several trace-reality lemmas;
     private declarations are not reusable, so the required restrictions are proved here.
   * Pinned Mathlib provides
     `LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range`, identifying an
     idempotent symmetric linear map with the orthogonal projection onto its range. It is
     applied after the concrete measurement range is identified below. -/

open scoped BigOperators ComplexOrder InnerProductSpace Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.BasisMeasurementProjection

open D5.S3.Observer.Conditioning
open D5.S3.Observer.Conditioning.UnreadStateOrthogonalProjection
open D5.S3.Quantum.Tomography.RankOneContextCommutator

variable {d : Nat} [NeZero d]

local instance matrixNormedAddCommGroup :
    NormedAddCommGroup (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one

local instance matrixComplexInnerProductSpace :
    InnerProductSpace ℂ (Matrix (Fin d) (Fin d) ℂ) :=
  Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

local instance matrixRealInnerProductSpace :
    InnerProductSpace ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  InnerProductSpace.rclikeToReal ℂ (Matrix (Fin d) (Fin d) ℂ)

/-- Hermitian matrices, regarded as a real inner-product subspace of complex matrices. -/
def HermitianSpace (d : Nat) : Submodule ℝ (Matrix (Fin d) (Fin d) ℂ) :=
  selfAdjoint.submodule ℝ (Matrix (Fin d) (Fin d) ℂ)

/-- A basis projector as a vector in the real Hermitian operator space. -/
def basisProjector (B : RankOneContext d) (j : Fin d) : HermitianSpace d := by
  refine ⟨B.projector j, ?_⟩
  change star (B.projector j) = B.projector j
  simpa only [Matrix.star_eq_conjTranspose] using (B.rankOne j).1

omit [NeZero d] in
@[simp]
theorem basisProjector_val (B : RankOneContext d) (j : Fin d) :
    (basisProjector B j).1 = B.projector j := rfl

/-- The real subspace of Hermitian matrices diagonal in the context `B`. -/
def diagonalSubspace (B : RankOneContext d) : Submodule ℝ (HermitianSpace d) :=
  Submodule.span ℝ (Set.range (basisProjector B))

/-- Unread rank-one basis measurement as a real-linear operator on Hermitian matrices. -/
noncomputable def basisMeasurement (B : RankOneContext d) :
    HermitianSpace d →ₗ[ℝ] HermitianSpace d := by
  refine
    { toFun := fun A => ⟨unreadState B.projector A.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · classical
    change (unreadState B.projector A.1)ᴴ = unreadState B.projector A.1
    rw [unreadState, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hP : (B.projector j)ᴴ = B.projector j := (B.rankOne j).1
    have hA : A.1ᴴ = A.1 := by
      have hAstar := A.2
      change star A.1 = A.1 at hAstar
      simpa only [Matrix.star_eq_conjTranspose] using hAstar
    simp only [Matrix.conjTranspose_mul, hP, hA, Matrix.mul_assoc]
  · intro A C
    apply Subtype.ext
    classical
    simp [unreadState, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  · intro r A
    apply Subtype.ext
    classical
    simp [unreadState, Finset.smul_sum]

omit [NeZero d] in
@[simp]
theorem basisMeasurement_val (B : RankOneContext d) (A : HermitianSpace d) :
    (basisMeasurement B A).1 = unreadState B.projector A.1 := rfl

omit [NeZero d] in
/-- Basis measurement preserves the matrix trace. -/
theorem basis_measurement_trace (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (A : HermitianSpace d) :
    Matrix.trace (basisMeasurement B A).1 = Matrix.trace A.1 := by
  change Matrix.trace (unreadState B.projector A.1) = Matrix.trace A.1
  exact unreadState_trace hB A.1

/-- The trace-zero Hermitian operator subspace. -/
def traceZeroHermitian (d : Nat) : Submodule ℝ (HermitianSpace d) where
  carrier := {A | Matrix.trace A.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro A C hA hC
    change Matrix.trace (A.1 + C.1) = 0
    rw [Matrix.trace_add, hA, hC, add_zero]
  smul_mem' := by
    intro r A hA
    change Matrix.trace ((r : ℂ) • A.1) = 0
    rw [Matrix.trace_smul, hA, smul_zero]

/-- Restriction of basis measurement to trace-zero Hermitian matrices. -/
noncomputable def traceZeroBasisMeasurement (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    traceZeroHermitian d →ₗ[ℝ] traceZeroHermitian d := by
  refine
    { toFun := fun A => ⟨basisMeasurement B A.1, ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · change Matrix.trace (basisMeasurement B A.1).1 = 0
    rw [basis_measurement_trace B hB A.1, A.2]
  · intro A C
    apply Subtype.ext
    exact (basisMeasurement B).map_add A.1 C.1
  · intro r A
    apply Subtype.ext
    exact (basisMeasurement B).map_smul r A.1

/-- The trace-zero diagonal subspace inside the trace-zero Hermitian carrier. -/
def diagonalTraceZeroSubspace (B : RankOneContext d) :
    Submodule ℝ (traceZeroHermitian d) where
  carrier := {A | A.1 ∈ diagonalSubspace B}
  zero_mem' := by
    change (0 : HermitianSpace d) ∈ diagonalSubspace B
    exact Submodule.zero_mem _
  add_mem' := by
    intro A C hA hC
    change A.1 + C.1 ∈ diagonalSubspace B
    exact Submodule.add_mem _ hA hC
  smul_mem' := by
    intro r A hA
    change r • A.1 ∈ diagonalSubspace B
    exact Submodule.smul_mem _ r hA

omit [NeZero d] in
private theorem matrix_inner_eq_trace_conjTranspose_mul
    (A C : Matrix (Fin d) (Fin d) ℂ) :
    inner ℂ A C = Matrix.trace (Aᴴ * C) := by
  change Matrix.trace (C * 1 * Aᴴ) = Matrix.trace (Aᴴ * C)
  rw [Matrix.mul_one, Matrix.trace_mul_comm]

omit [NeZero d] in
private theorem trace_projector_mul_real (B : RankOneContext d)
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
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hstar
    change (starRingEnd ℂ (Matrix.trace (B.projector j * A.1))).im = _ at him
    rw [Complex.conj_im] at him
    simpa using (show (Matrix.trace (B.projector j * A.1)).im = 0 by linarith)

omit [NeZero d] in
private theorem basis_measurement_eq_projector_sum (B : RankOneContext d)
    (A : HermitianSpace d) :
    basisMeasurement B A =
      ∑ j, (Matrix.trace (B.projector j * A.1)).re • basisProjector B j := by
  apply Subtype.ext
  simp only [basisMeasurement_val, Submodule.coe_sum, Submodule.coe_smul,
    basisProjector_val]
  change unreadState B.projector A.1 =
    ∑ j, (Matrix.trace (B.projector j * A.1)).re • B.projector j
  rw [unreadState]
  apply Finset.sum_congr rfl
  intro j _
  rw [(B.rankOne j).2.2.2 A.1, trace_projector_mul_real B A j]
  rfl

omit [NeZero d] in
private theorem basis_measurement_projector (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) (j : Fin d) :
    basisMeasurement B (basisProjector B j) = basisProjector B j := by
  apply Subtype.ext
  change unreadState B.projector (B.projector j) = B.projector j
  apply (unreadState_fixed_iff hB (B.projector j)).2
  intro i k hik
  by_cases hij : i = j
  · subst i
    rw [hB.idempotent j, hB.orthogonal j k hik]
  · rw [hB.orthogonal i j hij, Matrix.zero_mul]

omit [NeZero d] in
private theorem basis_measurement_idempotent (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    IsIdempotentElem (basisMeasurement B) := by
  apply LinearMap.ext
  intro A
  apply Subtype.ext
  change unreadState B.projector (unreadState B.projector A.1) =
    unreadState B.projector A.1
  exact unreadState_idempotent hB A.1

omit [NeZero d] in
private theorem basis_measurement_symmetric (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    (basisMeasurement B).IsSymmetric := by
  intro A C
  change (inner ℂ (basisMeasurement B A).1 C.1).re =
    (inner ℂ A.1 (basisMeasurement B C).1).re
  rw [matrix_inner_eq_trace_conjTranspose_mul,
    matrix_inner_eq_trace_conjTranspose_mul]
  exact congrArg Complex.re
    ((unread_state_orthogonal_projection hB).2.1 A.1 C.1)

omit [NeZero d] in
private theorem basis_measurement_symmetric_projection (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    (basisMeasurement B).IsSymmetricProjection :=
  ⟨basis_measurement_idempotent B hB, basis_measurement_symmetric B hB⟩

omit [NeZero d] in
theorem basis_measurement_range (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    LinearMap.range (basisMeasurement B) = diagonalSubspace B := by
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    rw [basis_measurement_eq_projector_sum]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    exact ⟨basisProjector B j, basis_measurement_projector B hB j⟩

omit [NeZero d] in
/-- A complete rank-one basis measurement is exactly the Hilbert--Schmidt orthogonal projection
onto its diagonal Hermitian subspace: it is idempotent and self-adjoint, has exactly that range,
and its discarded component is orthogonal to every diagonal Hermitian matrix. -/
theorem basis_measurement_is_orthogonal_projection (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    (basisMeasurement B).IsSymmetricProjection ∧
      LinearMap.range (basisMeasurement B) = diagonalSubspace B ∧
      (∀ A D : HermitianSpace d, D ∈ diagonalSubspace B →
        inner ℝ (A - basisMeasurement B A) D = 0) := by
  have hProjection := basis_measurement_symmetric_projection B hB
  have hRange := basis_measurement_range B hB
  refine ⟨hProjection, hRange, ?_⟩
  intro A D hD
  have hDRange : D ∈ LinearMap.range (basisMeasurement B) := by
    rw [hRange]
    exact hD
  rcases LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hProjection with
    ⟨hRangeProjection, hEq⟩
  letI : (LinearMap.range (basisMeasurement B)).HasOrthogonalProjection := hRangeProjection
  rw [hEq]
  exact Submodule.starProjection_inner_eq_zero A D hDRange

omit [NeZero d] in
/-- On trace-zero Hermitian matrices, basis measurement is the orthogonal projection onto the
trace-zero diagonal subspace, with exact range rather than mere range containment. -/
theorem trace_zero_basis_measurement_is_orthogonal_projection (B : RankOneContext d)
    (hB : IsRecordMeasurement B.projector) :
    (traceZeroBasisMeasurement B hB).IsSymmetricProjection ∧
      LinearMap.range (traceZeroBasisMeasurement B hB) = diagonalTraceZeroSubspace B := by
  constructor
  · constructor
    · apply LinearMap.ext
      intro A
      apply Subtype.ext
      change basisMeasurement B (basisMeasurement B A.1) = basisMeasurement B A.1
      apply Subtype.ext
      change unreadState B.projector (unreadState B.projector A.1.1) =
        unreadState B.projector A.1.1
      exact unreadState_idempotent hB A.1.1
    · intro A C
      change inner ℝ (basisMeasurement B A.1) C.1 =
        inner ℝ A.1 (basisMeasurement B C.1)
      exact basis_measurement_symmetric B hB A.1 C.1
  · apply le_antisymm
    · rintro _ ⟨A, rfl⟩
      change basisMeasurement B A.1 ∈ diagonalSubspace B
      rw [← basis_measurement_range B hB]
      exact ⟨A.1, rfl⟩
    · intro D hD
      change D.1 ∈ diagonalSubspace B at hD
      rw [← basis_measurement_range B hB] at hD
      rcases hD with ⟨A, hA⟩
      have hTraceA : Matrix.trace A.1 = 0 := by
        rw [← basis_measurement_trace B hB A, hA]
        exact D.2
      refine ⟨⟨A, hTraceA⟩, ?_⟩
      apply Subtype.ext
      exact hA

example : ∃ B : RankOneContext 1, IsRecordMeasurement B.projector ∧
    (basisMeasurement B).IsSymmetricProjection := by
  let B : RankOneContext 1 :=
    { projector := fun _ => 1
      rankOne := by
        intro j
        refine ⟨by simp, by simp, by simp, ?_⟩
        intro X
        ext i k
        fin_cases i
        fin_cases k
        simp [Matrix.trace, Matrix.mul_apply]
      resolvesIdentity := by simp }
  have hB : IsRecordMeasurement B.projector := by
    refine ⟨?_, ?_, ?_, B.resolvesIdentity⟩
    · intro j
      simpa only [Matrix.star_eq_conjTranspose] using (B.rankOne j).1
    · intro j
      exact (B.rankOne j).2.1
    · intro j k hjk
      exact (hjk (Subsingleton.elim j k)).elim
  exact ⟨B, hB, (basis_measurement_is_orthogonal_projection B hB).1⟩

#print axioms basis_measurement_is_orthogonal_projection
#print axioms trace_zero_basis_measurement_is_orthogonal_projection

end D5.S3.Quantum.Measurement.BasisMeasurementProjection
