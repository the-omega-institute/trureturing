/- GID: D5/S3/ContinuousObservables/CentralWinding
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exhibit finite cyclic winding updates whose cardinal power is a central phase. -/

import D5.S3.ContinuousObservables.PhaseFunctionCenter
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace D5.S3.ContinuousObservables.CentralWinding

open scoped BigOperators
open D5.S3.ContinuousObservables.PhaseFunctionCenter

/- Library-search audit trail (2026-08-12):
   * Searches of the pinned Mathlib tree for weighted cyclic shifts, monomial matrices, companion
     matrix power formulas, and winding-number certificates found no theorem with this conclusion.
   * `AddCircle.toCircle`, `Circle.coe_exp`, permutation matrices, `Unitary.mem_iff`,
     `Finset.prod_eq_single`, and `ZMod.natCast_zmod_val` are reused below.
   * The imported phase-function center classification supplies the ambient continuous-observable
     setting. The proof is uniform in every cyclic cardinality `M` with `2 <= M`; `M = 2` remains
     as an explicit matrix witness. -/

/-- Continuous `M`-by-`M` matrix fields over the visible phase circle. -/
abbrev CyclicObservable (M : ℕ) [NeZero M] :=
  C(AddCircle (1 : ℝ), Matrix (ZMod M) (ZMod M) ℂ)

/-- The visible circle coordinate, regarded as a complex-valued continuous phase. -/
noncomputable def windingPhase : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun phase => (AddCircle.toCircle phase : ℂ),
    continuous_subtype_val.comp AddCircle.continuous_toCircle⟩

/-- The visible winding phase embedded as a scalar cyclic-window matrix field. -/
noncomputable def windingPhaseObservable (M : ℕ) [NeZero M] : CyclicObservable M :=
  phaseScalarObservable (M := M) windingPhase

/-- The cyclic row permutation used by the winding update. -/
private def windingPerm (M : ℕ) : Equiv.Perm (ZMod M) :=
  Equiv.subRight 1

/-- The phase weight occurs only on the row-zero wrap edge. -/
private noncomputable def windingWeight {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) (i : ZMod M) : ℂ :=
  if i = 0 then windingPhase phase else 1

/-- A cyclic `M`-point update with the visible phase on its single wrap edge. -/
noncomputable def windingShiftObservable (M : ℕ) [NeZero M] : CyclicObservable M :=
  ⟨fun phase =>
      Matrix.diagonal (windingWeight (M := M) phase) * (windingPerm M).permMatrix ℂ, by
    apply continuous_matrix
    intro i j
    simp only [Matrix.diagonal_mul, windingPerm, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]
    by_cases hi : i = 0
    · subst i
      by_cases hj : (-1 : ZMod M) = j
      · simp [windingWeight, hj, windingPhase.continuous]
      · simpa [windingWeight, hj] using
          (continuous_const : Continuous fun _ : AddCircle (1 : ℝ) => (0 : ℂ))
    · by_cases hij : i - 1 = j
      · simpa [windingWeight, hi, hij] using
          (continuous_const : Continuous fun _ : AddCircle (1 : ℝ) => (1 : ℂ))
      · simpa [windingWeight, hi, hij] using
          (continuous_const : Continuous fun _ : AddCircle (1 : ℝ) => (0 : ℂ))⟩

private theorem winding_shift_mulVec {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) (v : ZMod M → ℂ) (i : ZMod M) :
    Matrix.mulVec (windingShiftObservable M phase) v i =
      windingWeight phase i * v (i - 1) := by
  rw [show windingShiftObservable M phase =
      Matrix.diagonal (windingWeight phase) * (windingPerm M).permMatrix ℂ by rfl,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.permMatrix_mulVec]
  rfl

private theorem winding_shift_pow_mulVec {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) (n : ℕ) (v : ZMod M → ℂ) (i : ZMod M) :
    Matrix.mulVec ((windingShiftObservable M phase) ^ n) v i =
      (∏ k ∈ Finset.range n, windingWeight phase (i - (k : ZMod M))) *
        v (i - (n : ZMod M)) := by
  induction n generalizing i v with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, ih, winding_shift_mulVec]
      simp only [Nat.cast_succ, Finset.prod_range_succ]
      ring_nf

private theorem winding_weight_prod {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) (i : ZMod M) :
    (∏ k ∈ Finset.range M, windingWeight phase (i - (k : ZMod M))) =
      windingPhase phase := by
  rw [Finset.prod_eq_single i.val]
  · simp [windingWeight, i.natCast_zmod_val]
  · intro k hk hki
    have hklt : k < M := Finset.mem_range.mp hk
    have hcast : i ≠ (k : ZMod M) := by
      intro h
      have hval := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hklt] at hval
      exact hki hval.symm
    simp [windingWeight, sub_ne_zero.mpr hcast]
  · exact fun h => (h (Finset.mem_range.mpr i.val_lt)).elim

private theorem winding_shift_matrix_pow_card {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) :
    (windingShiftObservable M phase) ^ M =
      Matrix.scalar (ZMod M) (windingPhase phase) := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  funext i
  rw [winding_shift_pow_mulVec, winding_weight_prod,
    Matrix.scalar_apply, Matrix.mulVec_diagonal]
  congr 1
  simp

/-- One full circuit of an `M`-point winding update accumulates exactly one visible phase. -/
theorem winding_shift_pow_card {M : ℕ} [NeZero M] :
    windingShiftObservable M ^ M = windingPhaseObservable M := by
  apply ContinuousMap.ext
  intro phase
  exact winding_shift_matrix_pow_card (M := M) phase

/-- The visible winding phase is central in every nonempty cyclic-window algebra. -/
theorem winding_phase_observable_mem_center {M : ℕ} [NeZero M] :
    windingPhaseObservable M ∈ Set.center (CyclicObservable M) := by
  rw [continuous_window_center_eq_phase_functions]
  exact ⟨windingPhase, rfl⟩

/-- The cardinal power of the winding update is central. -/
theorem winding_shift_pow_card_mem_center {M : ℕ} [NeZero M] :
    windingShiftObservable M ^ M ∈ Set.center (CyclicObservable M) := by
  rw [winding_shift_pow_card]
  exact winding_phase_observable_mem_center

private theorem windingPhase_star_mul (phase : AddCircle (1 : ℝ)) :
    (starRingEnd ℂ) (windingPhase phase) * windingPhase phase = 1 := by
  simpa [windingPhase, RCLike.star_def, Circle.norm_coe] using
    (RCLike.conj_mul (AddCircle.toCircle phase : ℂ))

private theorem windingPhase_mul_star (phase : AddCircle (1 : ℝ)) :
    windingPhase phase * (starRingEnd ℂ) (windingPhase phase) = 1 := by
  simpa [windingPhase, RCLike.star_def, Circle.norm_coe] using
    (RCLike.mul_conj (AddCircle.toCircle phase : ℂ))

private theorem windingWeight_star_mul {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) (i : ZMod M) :
    star (windingWeight phase i) * windingWeight phase i = 1 := by
  by_cases hi : i = 0
  · simpa [windingWeight, hi] using windingPhase_star_mul phase
  · simp [windingWeight, hi]

private theorem windingWeight_mul_star {M : ℕ} [NeZero M]
    (phase : AddCircle (1 : ℝ)) (i : ZMod M) :
    windingWeight phase i * star (windingWeight phase i) = 1 := by
  by_cases hi : i = 0
  · simpa [windingWeight, hi] using windingPhase_mul_star phase
  · simp [windingWeight, hi]

/-- Every finite cyclic winding update is unitary. -/
theorem winding_shift_unitary {M : ℕ} [NeZero M] :
    windingShiftObservable M ∈ unitary (CyclicObservable M) := by
  rw [Unitary.mem_iff]
  constructor
  · apply ContinuousMap.ext
    intro phase
    simp only [ContinuousMap.star_apply, ContinuousMap.mul_apply, ContinuousMap.one_apply]
    rw [show windingShiftObservable M phase =
        Matrix.diagonal (windingWeight phase) * (windingPerm M).permMatrix ℂ by rfl]
    rw [star_mul, Matrix.star_eq_conjTranspose ((windingPerm M).permMatrix ℂ),
      Matrix.star_eq_conjTranspose (Matrix.diagonal _), Matrix.diagonal_conjTranspose,
      Matrix.conjTranspose_permMatrix, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (star (windingWeight phase)) i * windingWeight phase i) = 1 by
      funext i
      exact windingWeight_star_mul phase i]
    rw [show Matrix.diagonal (1 : ZMod M → ℂ) = 1 by exact Matrix.diagonal_one,
      Matrix.one_mul]
    change (windingPerm M)⁻¹.permMatrix ℂ * (windingPerm M).permMatrix ℂ = 1
    rw [← Matrix.permMatrix_mul]
    simp
  · apply ContinuousMap.ext
    intro phase
    simp only [ContinuousMap.star_apply, ContinuousMap.mul_apply, ContinuousMap.one_apply]
    rw [show windingShiftObservable M phase =
        Matrix.diagonal (windingWeight phase) * (windingPerm M).permMatrix ℂ by rfl]
    rw [star_mul, Matrix.star_eq_conjTranspose ((windingPerm M).permMatrix ℂ),
      Matrix.star_eq_conjTranspose (Matrix.diagonal _), Matrix.diagonal_conjTranspose,
      Matrix.conjTranspose_permMatrix, Matrix.mul_assoc (Matrix.diagonal (windingWeight phase)),
      ← Matrix.mul_assoc ((windingPerm M).permMatrix ℂ), ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
    rw [show (fun i => windingWeight phase i * (star (windingWeight phase)) i) = 1 by
      funext i
      exact windingWeight_mul_star phase i]
    simp

/-- The central winding phase is itself unitary in every cyclic-window algebra. -/
theorem winding_phase_observable_unitary {M : ℕ} [NeZero M] :
    windingPhaseObservable M ∈ unitary (CyclicObservable M) := by
  rw [← winding_shift_pow_card]
  exact (unitary (CyclicObservable M)).pow_mem winding_shift_unitary M

private theorem windingPhase_zero :
    windingPhase (0 : AddCircle (1 : ℝ)) = 1 := by
  simp [windingPhase]

private theorem windingPhase_half_turn :
    windingPhase ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = -1 := by
  change ((AddCircle.toCircle ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) : Circle) : ℂ) = -1
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  rw [show ((2 * Real.pi / 1 * (1 / 2) : ℝ) : ℂ) * Complex.I =
      Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- The chosen phase takes distinct values at zero and the half-turn. This excludes every
constant, winding-free phase configuration, which would take equal values at those points. -/
theorem winding_phase_nonconstant :
    windingPhase (0 : AddCircle (1 : ℝ)) ≠
      windingPhase ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [windingPhase_zero, windingPhase_half_turn]
  norm_num

/-- The central winding phase is not the constant identity field. -/
theorem winding_phase_observable_ne_one {M : ℕ} [NeZero M] :
    windingPhaseObservable M ≠ (1 : CyclicObservable M) := by
  intro h
  have hphase := congrArg
    (fun A : CyclicObservable M => A ((1 / 2 : ℝ) : AddCircle (1 : ℝ))) h
  have hentry := congrArg (fun A : Matrix (ZMod M) (ZMod M) ℂ => A 0 0) hphase
  have hentry' : windingPhase ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 1 := by
    simpa [windingPhaseObservable, phaseScalarObservable, Matrix.scalar_apply] using hentry
  rw [windingPhase_half_turn] at hentry'
  norm_num at hentry'

/-- For `M >= 2`, the winding update itself is noncentral, witnessed against a constant
diagonal field at the wrap entry `(0, -1)`. -/
theorem winding_shift_not_mem_center {M : ℕ} [NeZero M] (hM : 2 ≤ M) :
    windingShiftObservable M ∉ Set.center (CyclicObservable M) := by
  letI : Fact (1 < M) := ⟨by omega⟩
  intro h
  rw [Semigroup.mem_center_iff] at h
  let diagonalWitness : CyclicObservable M :=
    ContinuousMap.const (AddCircle (1 : ℝ))
      (Matrix.diagonal fun i : ZMod M => if i = 0 then (1 : ℂ) else 0)
  have hcomm := h diagonalWitness
  have hphase := congrArg (fun A : CyclicObservable M => A 0) hcomm
  have hentry := congrArg
    (fun A : Matrix (ZMod M) (ZMod M) ℂ => A 0 (-1)) hphase
  have hneg : (-1 : ZMod M) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  simp only [diagonalWitness, ContinuousMap.const_apply, ContinuousMap.mul_apply,
    windingShiftObservable, Matrix.diagonal_mul, Matrix.mul_diagonal, windingPerm] at hentry
  simp [windingWeight, hneg, windingPhase_zero] at hentry

/-- For every cyclic cardinality `M >= 2`, the winding update is a noncentral unitary whose
`M`-th power is a nonidentity central unitary phase. The final clause pins the chosen phase as
nonconstant, ruling out every constant, winding-free configuration. -/
theorem central_winding_certificate {M : ℕ} [NeZero M] (hM : 2 ≤ M) :
    windingShiftObservable M ^ M = windingPhaseObservable M ∧
      windingShiftObservable M ^ M ∈ Set.center (CyclicObservable M) ∧
      windingPhaseObservable M ∈ Set.center (CyclicObservable M) ∧
      windingShiftObservable M ∈ unitary (CyclicObservable M) ∧
      windingPhaseObservable M ∈ unitary (CyclicObservable M) ∧
      windingPhaseObservable M ≠ (1 : CyclicObservable M) ∧
      windingShiftObservable M ∉ Set.center (CyclicObservable M) ∧
      windingPhase (0 : AddCircle (1 : ℝ)) ≠
        windingPhase ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) :=
  ⟨winding_shift_pow_card, winding_shift_pow_card_mem_center,
    winding_phase_observable_mem_center, winding_shift_unitary,
    winding_phase_observable_unitary, winding_phase_observable_ne_one,
    winding_shift_not_mem_center hM, winding_phase_nonconstant⟩

/-- Continuous two-by-two matrix fields, retained as the smallest honest winding witness. -/
abbrev TwoPointObservable := CyclicObservable 2

/-- At `M = 2`, the general update is exactly the concrete matrix `[[0,z],[1,0]]`. -/
theorem winding_shift_two_point_apply (phase : AddCircle (1 : ℝ)) :
    windingShiftObservable 2 phase = !![0, windingPhase phase; 1, 0] := by
  have h01 : (0 : ZMod 2) - 1 = 1 := by decide
  have hne : (1 : ZMod 2) ≠ 0 := by decide
  have hentry00 : windingShiftObservable 2 phase 0 0 = 0 := by
    simp [windingShiftObservable, windingWeight, windingPerm, Matrix.diagonal_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]
  have hentry01 : windingShiftObservable 2 phase 0 1 = windingPhase phase := by
    simp [windingShiftObservable, windingWeight, windingPerm, Matrix.diagonal_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      h01]
  have hentry10 : windingShiftObservable 2 phase 1 0 = 1 := by
    simp [windingShiftObservable, windingWeight, windingPerm, Matrix.diagonal_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      hne]
  have hentry11 : windingShiftObservable 2 phase 1 1 = 0 := by
    simp [windingShiftObservable, windingWeight, windingPerm, Matrix.diagonal_mul,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      hne]
  ext i j
  fin_cases i <;> fin_cases j
  · exact hentry00
  · exact hentry01
  · exact hentry10
  · exact hentry11

/-- The explicit two-point instance of the general finite-cyclic winding certificate. -/
theorem central_winding_two_point_certificate :
    windingShiftObservable 2 ^ 2 = windingPhaseObservable 2 ∧
      windingShiftObservable 2 ^ 2 ∈ Set.center TwoPointObservable ∧
      windingPhaseObservable 2 ∈ Set.center TwoPointObservable ∧
      windingShiftObservable 2 ∈ unitary TwoPointObservable ∧
      windingPhaseObservable 2 ∈ unitary TwoPointObservable ∧
      windingPhaseObservable 2 ≠ (1 : TwoPointObservable) ∧
      windingShiftObservable 2 ∉ Set.center TwoPointObservable ∧
      windingPhase (0 : AddCircle (1 : ℝ)) ≠
        windingPhase ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) :=
  central_winding_certificate (M := 2) (by norm_num)

end D5.S3.ContinuousObservables.CentralWinding
