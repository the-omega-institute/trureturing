/- GID: D5/S3/Observer/Conditioning
   generality: G
   mirror-B: D5/B/S3/Observer/Conditioning
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formalize finite record conditioning and unread measurement states. -/

/- Library-search audit trail (2026-08-07):
   * Local mathlib and D5 searches for `pinching`, `Lueders`, `projective measurement`,
     `projection-valued measurement`, `unread state`, and quantum conditional expectation found no
     equivalent finite-dimensional matrix theorem.
   * The proof reuses `Matrix.trace_sum`, `Matrix.trace_smul`, `Matrix.trace_mul_comm`,
     `Matrix.trace_mul_cycle`, `Matrix.sum_mul`, `Matrix.mul_sum`, and
     `Matrix.PosSemidef.mul_mul_conjTranspose_same` from mathlib, plus the projection-weight
     nonnegativity established in `FiniteDimensional.born_probability_skeleton`.
-/

import D5.S3.Quantum.FiniteDimensional

namespace D5.S3.Observer.Conditioning

open D5.S3.Quantum.FiniteDimensional
open scoped BigOperators ComplexOrder

variable {n kappa : Type*} [Fintype n] [DecidableEq n]
    [Fintype kappa] [decEqKappa : DecidableEq kappa]
    {P : kappa -> Matrix n n ℂ}

/-- A finite complete family of pairwise orthogonal self-adjoint projections. -/
structure IsRecordMeasurement (P : kappa -> Matrix n n ℂ) : Prop where
  selfAdjoint : forall k, star (P k) = P k
  idempotent : forall k, P k * P k = P k
  orthogonal : forall k l, k ≠ l -> P k * P l = 0
  complete : ∑ k, P k = 1

/-- The state obtained by measuring the record and then discarding its value. -/
def unreadState (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ k, P k * rho * P k

/-- The trace weight of a record outcome. -/
noncomputable def recordWeight (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ)
    (k : kappa) : ℂ :=
  bornProbability rho (P k)

omit decEqKappa in
/-- Record weights sum to the trace of the original matrix. -/
theorem recordWeight_sum (hP : IsRecordMeasurement P) (rho : Matrix n n ℂ) :
    ∑ k, recordWeight P rho k = Matrix.trace rho := by
  classical
  calc
    ∑ k, recordWeight P rho k = Matrix.trace (∑ k, rho * P k) := by
      simp [recordWeight, bornProbability, Matrix.trace_sum]
    _ = Matrix.trace (rho * ∑ k, P k) := by rw [Matrix.mul_sum]
    _ = Matrix.trace rho := by rw [hP.complete, Matrix.mul_one]

omit decEqKappa in
/-- Discarding a record preserves trace. -/
theorem unreadState_trace (hP : IsRecordMeasurement P) (rho : Matrix n n ℂ) :
    Matrix.trace (unreadState P rho) = Matrix.trace rho := by
  classical
  rw [unreadState, Matrix.trace_sum]
  calc
    ∑ k, Matrix.trace (P k * rho * P k) =
        ∑ k, Matrix.trace (rho * P k) := by
      apply Finset.sum_congr rfl
      intro k _
      calc
        Matrix.trace (P k * rho * P k) = Matrix.trace (P k * P k * rho) :=
          Matrix.trace_mul_cycle (P k) rho (P k)
        _ = Matrix.trace (P k * rho) := by rw [hP.idempotent k]
        _ = Matrix.trace (rho * P k) := Matrix.trace_mul_comm (P k) rho
    _ = Matrix.trace rho := by
      simpa [recordWeight, bornProbability] using recordWeight_sum hP rho

omit decEqKappa in
private theorem left_project_unread (hP : IsRecordMeasurement P)
    (rho : Matrix n n ℂ) (k : kappa) :
    P k * unreadState P rho = P k * rho * P k := by
  classical
  rw [unreadState, Matrix.mul_sum]
  calc
    ∑ l, P k * (P l * rho * P l) = P k * (P k * rho * P k) := by
      apply Finset.sum_eq_single k
      · intro l _ hl
        calc
          P k * (P l * rho * P l) = (P k * P l) * rho * P l := by
            simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hP.orthogonal k l hl.symm, Matrix.zero_mul, Matrix.zero_mul]
      · simp
    _ = P k * rho * P k := by
      calc
        P k * (P k * rho * P k) = (P k * P k) * rho * P k := by
          simp only [Matrix.mul_assoc]
        _ = P k * rho * P k := by rw [hP.idempotent k]

omit decEqKappa in
/-- Forgetting the outcome twice is the same as forgetting it once. -/
theorem unreadState_idempotent (hP : IsRecordMeasurement P) (rho : Matrix n n ℂ) :
    unreadState P (unreadState P rho) = unreadState P rho := by
  classical
  change (∑ k, P k * unreadState P rho * P k) = unreadState P rho
  apply Finset.sum_congr rfl
  intro k _
  rw [left_project_unread hP rho k, Matrix.mul_assoc, hP.idempotent k]

omit decEqKappa in
/-- The unread state is fixed exactly when all off-diagonal record blocks vanish. -/
theorem unreadState_fixed_iff (hP : IsRecordMeasurement P) (rho : Matrix n n ℂ) :
    unreadState P rho = rho <->
      forall k l, k ≠ l -> P k * rho * P l = 0 := by
  classical
  constructor
  · intro hFixed k l hkl
    rw [← hFixed, left_project_unread hP rho k, Matrix.mul_assoc,
      hP.orthogonal k l hkl, Matrix.mul_zero]
  · intro hOffDiagonal
    have hRow (k : kappa) : P k * rho = P k * rho * P k := by
      calc
        P k * rho = P k * rho * 1 := by rw [Matrix.mul_one]
        _ = P k * rho * (∑ l, P l) := by rw [hP.complete]
        _ = ∑ l, P k * rho * P l := by rw [Matrix.mul_sum]
        _ = P k * rho * P k := by
          apply Finset.sum_eq_single k
          · intro l _ hl
            exact hOffDiagonal k l hl.symm
          · simp
    calc
      unreadState P rho = ∑ k, P k * rho * P k := rfl
      _ = ∑ k, P k * rho := by
        apply Finset.sum_congr rfl
        intro k _
        exact (hRow k).symm
      _ = (∑ k, P k) * rho := by rw [Matrix.sum_mul]
      _ = rho := by rw [hP.complete, Matrix.one_mul]

/-- The normalized state conditioned on a nonzero record outcome. -/
noncomputable def conditionalState (P : kappa -> Matrix n n ℂ) (rho : Matrix n n ℂ)
    (k : kappa) : Matrix n n ℂ :=
  (recordWeight P rho k)⁻¹ • (P k * rho * P k)

omit decEqKappa in
/-- A nonzero conditional branch is positive semidefinite and has trace one. -/
theorem conditionalState_isState (hP : IsRecordMeasurement P) {rho : Matrix n n ℂ}
    (hRho : rho.PosSemidef) (hTr : Matrix.trace rho = 1) {k : kappa}
    (hk : recordWeight P rho k ≠ 0) :
    (conditionalState P rho k).PosSemidef /\
      Matrix.trace (conditionalState P rho k) = 1 := by
  have hConjTranspose : Matrix.conjTranspose (P k) = P k := by
    simpa only [Matrix.star_eq_conjTranspose] using hP.selfAdjoint k
  have hCompressed : (P k * rho * P k).PosSemidef := by
    simpa only [hConjTranspose] using hRho.mul_mul_conjTranspose_same (P k)
  have hTraceCompressed :
      Matrix.trace (P k * rho * P k) = recordWeight P rho k := by
    rw [recordWeight]
    calc
      Matrix.trace (P k * rho * P k) = Matrix.trace (P k * P k * rho) :=
        Matrix.trace_mul_cycle (P k) rho (P k)
      _ = Matrix.trace (P k * rho) := by rw [hP.idempotent k]
      _ = Matrix.trace (rho * P k) := Matrix.trace_mul_comm (P k) rho
  have hWeightNonneg : 0 <= recordWeight P rho k := by
    have hBornNonneg :=
      (born_probability_skeleton rho hRho hTr).2.2 (P k)
        (hP.selfAdjoint k) (hP.idempotent k)
    simpa [recordWeight, bornProbability] using hBornNonneg
  constructor
  · exact hCompressed.smul (inv_nonneg.mpr hWeightNonneg)
  · rw [conditionalState, Matrix.trace_smul, hTraceCompressed]
    exact inv_mul_cancel₀ hk

omit decEqKappa in
private theorem compressed_eq_zero_of_recordWeight_eq_zero
    (hP : IsRecordMeasurement P) {rho : Matrix n n ℂ} (hRho : rho.PosSemidef)
    {k} (hk : recordWeight P rho k = 0) : P k * rho * P k = 0 := by
  have hConjTranspose : Matrix.conjTranspose (P k) = P k := by
    simpa only [Matrix.star_eq_conjTranspose] using hP.selfAdjoint k
  have hCompressed : (P k * rho * P k).PosSemidef := by
    simpa only [hConjTranspose] using hRho.mul_mul_conjTranspose_same (P k)
  apply hCompressed.trace_eq_zero_iff.mp
  rw [recordWeight] at hk
  calc
    Matrix.trace (P k * rho * P k) = Matrix.trace (P k * P k * rho) :=
      Matrix.trace_mul_cycle (P k) rho (P k)
    _ = Matrix.trace (P k * rho) := by rw [hP.idempotent k]
    _ = Matrix.trace (rho * P k) := Matrix.trace_mul_comm (P k) rho
    _ = 0 := hk

omit decEqKappa in
/-- The unread state of a positive matrix is its weighted conditional ensemble. -/
theorem unread_eq_weighted_ensemble (hP : IsRecordMeasurement P)
    {rho : Matrix n n ℂ} (hRho : rho.PosSemidef) :
    unreadState P rho = ∑ k, recordWeight P rho k • conditionalState P rho k := by
  classical
  unfold unreadState conditionalState
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : recordWeight P rho k = 0
  · rw [hk, zero_smul, compressed_eq_zero_of_recordWeight_eq_zero hP hRho hk]
  · rw [smul_smul, mul_inv_cancel₀ hk, one_smul]

end D5.S3.Observer.Conditioning
