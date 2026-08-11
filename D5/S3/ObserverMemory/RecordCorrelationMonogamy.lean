/- GID: D5/S3/ObserverMemory/RecordCorrelationMonogamy
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RecordCorrelationMonogamy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound complementary system correlations with one fixed record pointer. -/

/-
Library-search audit trail (2026-08-11):

* Searches of pinned mathlib and D5 for `correlation monogamy`, `complementary correlation`,
  `Pauli correlation`, `anticommuting expectation`, and variants found no theorem with this exact
  density-matrix statement.
* `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` supplies the structural step: zero weight on a
  basis vector of a positive semidefinite matrix forces the whole corresponding column to vanish.
  `Matrix.posSemidef_vecMulVec_self_star` supplies the rank-one anti-vacuity witness.
* Both correlations use the same record `Z` pointer. Replacing the second observable by `X tensor
  X` would make the claim false: a Bell state has perfect `Z tensor Z` and `X tensor X`
  correlations simultaneously.
-/

import D5.S3.Quantum.FiniteDimensional

namespace D5.S3.ObserverMemory.RecordCorrelationMonogamy

open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators
open scoped ComplexOrder
open scoped Kronecker

/-- The density-matrix carrier for one system qubit and one two-address record. -/
abbrev SystemRecordMatrix := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Correlation of a system observable with the fixed address observable of one record. -/
noncomputable def recordPointerCorrelation
    (rho : SystemRecordMatrix) (systemObservable : QubitMatrix) : ℝ :=
  (Matrix.trace (rho * (systemObservable ⊗ₖ qubitZ))).re

/-- Correlation between the system address and the record address. -/
noncomputable def addressCorrelation (rho : SystemRecordMatrix) : ℝ :=
  recordPointerCorrelation rho qubitZ

/-- Correlation between the conjugate system observable and the same record address. -/
noncomputable def conjugateCorrelation (rho : SystemRecordMatrix) : ℝ :=
  recordPointerCorrelation rho qubitX

/-- A classical joint system-record law, used only for the explicit numerical witness. -/
def classicalRecordState (weight : Fin 2 × Fin 2 → ℝ) : SystemRecordMatrix :=
  Matrix.diagonal fun ir => ((weight ir : ℝ) : ℂ)

/-- A nonnegative normalized classical law gives a positive trace-one record state. -/
theorem classical_record_state_is_density
    (weight : Fin 2 × Fin 2 → ℝ)
    (hweight : (∀ ir, 0 ≤ weight ir) ∧ ∑ ir, weight ir = 1) :
    (classicalRecordState weight).PosSemidef ∧
      Matrix.trace (classicalRecordState weight) = 1 := by
  constructor
  · rw [classicalRecordState, Matrix.posSemidef_diagonal_iff]
    intro ir
    exact_mod_cast hweight.1 ir
  · rw [classicalRecordState, Matrix.trace_diagonal]
    exact_mod_cast hweight.2

/-- The address correlation of a diagonal witness is its signed agreement probability. -/
theorem address_correlation_eq
    (weight : Fin 2 × Fin 2 → ℝ) :
    addressCorrelation (classicalRecordState weight) =
      weight (0, 0) - weight (0, 1) - weight (1, 0) + weight (1, 1) := by
  simp [addressCorrelation, recordPointerCorrelation, classicalRecordState, Matrix.trace,
    Matrix.mul_apply, qubitZ, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- A diagonal witness has no conjugate correlation with its fixed address pointer. -/
theorem conjugate_correlation_eq_zero
    (weight : Fin 2 × Fin 2 → ℝ) :
    conjugateCorrelation (classicalRecordState weight) = 0 := by
  simp [conjugateCorrelation, recordPointerCorrelation, classicalRecordState, Matrix.trace,
    Matrix.mul_apply, qubitX, qubitZ, Fintype.sum_prod_type, Fin.sum_univ_two]

private def basisVector (k : Fin 2 × Fin 2) : Fin 2 × Fin 2 → ℂ :=
  fun i => if i = k then 1 else 0

private theorem column_eq_zero_of_diagonal_eq_zero
    (rho : SystemRecordMatrix) (hRho : rho.PosSemidef) (k : Fin 2 × Fin 2)
    (hDiagonal : rho k k = 0) :
    Matrix.mulVec rho (basisVector k) = 0 := by
  apply (hRho.dotProduct_mulVec_zero_iff (basisVector k)).mp
  simp [basisVector, Matrix.mulVec, dotProduct, hDiagonal]

private theorem diagonal_eq_zero_of_re_eq_zero
    (rho : SystemRecordMatrix) (hRho : rho.PosSemidef) (k : Fin 2 × Fin 2)
    (hReal : (rho k k).re = 0) :
    rho k k = 0 := by
  apply Complex.ext
  · simpa using hReal
  · simp only [Complex.zero_im]
    have hSelfAdjoint := hRho.isHermitian.apply k k
    have hImag := congrArg Complex.im hSelfAdjoint
    simp only [Complex.star_def, Complex.conj_im] at hImag
    linarith

/--
For every joint density matrix, a perfect copy of the system `Z` address in one fixed record
pointer eliminates correlation of that same pointer with the conjugate system `X` observable.
-/
theorem record_correlation_monogamy
    (rho : SystemRecordMatrix)
    (hRho : rho.PosSemidef)
    (hTrace : Matrix.trace rho = 1)
    (hPerfect : addressCorrelation rho = 1) :
    conjugateCorrelation rho = 0 := by
  have hTraceReal :
      (rho (0, 0) (0, 0)).re + (rho (0, 1) (0, 1)).re +
          (rho (1, 0) (1, 0)).re + (rho (1, 1) (1, 1)).re = 1 := by
    simpa [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc] using
      congrArg Complex.re hTrace
  have hAddress := hPerfect
  simp [addressCorrelation, recordPointerCorrelation, Matrix.trace, Matrix.mul_apply, qubitZ,
    Fintype.sum_prod_type, Fin.sum_univ_two] at hAddress
  have h01Nonneg : 0 ≤ (rho (0, 1) (0, 1)).re :=
    (RCLike.nonneg_iff.mp
      (hRho.diag_nonneg (i := ((0, 1) : Fin 2 × Fin 2)))).1
  have h10Nonneg : 0 ≤ (rho (1, 0) (1, 0)).re :=
    (RCLike.nonneg_iff.mp
      (hRho.diag_nonneg (i := ((1, 0) : Fin 2 × Fin 2)))).1
  have h01Real : (rho (0, 1) (0, 1)).re = 0 := by
    linarith
  have h10Real : (rho (1, 0) (1, 0)).re = 0 := by
    linarith
  have h01 : rho (0, 1) (0, 1) = 0 :=
    diagonal_eq_zero_of_re_eq_zero rho hRho (0, 1) h01Real
  have h10 : rho (1, 0) (1, 0) = 0 :=
    diagonal_eq_zero_of_re_eq_zero rho hRho (1, 0) h10Real
  have hColumn01 := column_eq_zero_of_diagonal_eq_zero rho hRho (0, 1) h01
  have hColumn10 := column_eq_zero_of_diagonal_eq_zero rho hRho (1, 0) h10
  have h00_10 : rho (0, 0) (1, 0) = 0 := by
    have h := congrFun hColumn10 (0, 0)
    simpa [basisVector, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two] using h
  have h11_01 : rho (1, 1) (0, 1) = 0 := by
    have h := congrFun hColumn01 (1, 1)
    simpa [basisVector, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two] using h
  have h10_00 : rho (1, 0) (0, 0) = 0 := by
    have h := hRho.isHermitian.apply (0, 0) (1, 0)
    rw [h00_10] at h
    simpa using congrArg star h
  have h01_11 : rho (0, 1) (1, 1) = 0 := by
    have h := hRho.isHermitian.apply (0, 1) (1, 1)
    rw [h11_01] at h
    simpa using h.symm
  simp [conjugateCorrelation, recordPointerCorrelation, Matrix.trace, Matrix.mul_apply,
    qubitX, qubitZ, Fintype.sum_prod_type, Fin.sum_univ_two, h00_10, h10_00,
    h01_11, h11_01]

/-- The unnormalized vector `(ket 00) + (ket 10)`. -/
def coherentXRecordVector : Fin 2 × Fin 2 → ℂ :=
  fun ir => if ir.2 = 0 then 1 else 0

/-- The state `(ket +)(bra +) tensor (ket 0)(bra 0)`. -/
noncomputable def coherentXRecordState : SystemRecordMatrix :=
  (1 / 2 : ℝ) • Matrix.vecMulVec coherentXRecordVector (star coherentXRecordVector)

/--
Anti-vacuity certificate: a non-diagonal density matrix has unit conjugate correlation with the
fixed record pointer. Thus `conjugateCorrelation` is not identically zero on the general domain.
-/
theorem coherent_record_anti_vacuity_certificate :
    let rho := coherentXRecordState
    rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      rho (0, 0) (1, 0) ≠ 0 ∧
      addressCorrelation rho = 0 ∧ conjugateCorrelation rho = 1 := by
  dsimp
  constructor
  · exact (Matrix.posSemidef_vecMulVec_self_star coherentXRecordVector).smul (by norm_num)
  constructor
  · norm_num [coherentXRecordState, Matrix.trace, coherentXRecordVector,
      Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  constructor
  · norm_num [coherentXRecordState, coherentXRecordVector, Matrix.vecMulVec_apply]
  constructor <;>
    norm_num [addressCorrelation, conjugateCorrelation, recordPointerCorrelation,
      coherentXRecordState, coherentXRecordVector, Matrix.trace, Matrix.mul_apply,
      Matrix.vecMulVec_apply, qubitX, qubitZ, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- A noisy address ledger with total agreement `7/8` and disagreement `1/8`. -/
noncomputable def threeQuarterAddressWeight (ir : Fin 2 × Fin 2) : ℝ :=
  if ir.1 = ir.2 then 7 / 16 else 1 / 16

/-- The explicit noisy address record retains correlation `3/4` in the selected basis. -/
theorem three_quarter_address_record_certificate :
    let rho := classicalRecordState threeQuarterAddressWeight
    rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
      addressCorrelation rho = 3 / 4 ∧ conjugateCorrelation rho = 0 := by
  have hweight :
      (∀ ir, 0 ≤ threeQuarterAddressWeight ir) ∧
        ∑ ir, threeQuarterAddressWeight ir = 1 := by
    constructor
    · rintro ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> norm_num [threeQuarterAddressWeight]
    · rw [Fintype.sum_prod_type]
      norm_num [threeQuarterAddressWeight, Fin.sum_univ_two]
  have hDensity := classical_record_state_is_density threeQuarterAddressWeight hweight
  dsimp
  refine ⟨hDensity.1, hDensity.2, ?_, conjugate_correlation_eq_zero _⟩
  rw [address_correlation_eq]
  norm_num [threeQuarterAddressWeight]

end D5.S3.ObserverMemory.RecordCorrelationMonogamy
