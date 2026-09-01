/- GID: D5/S3/Weil/Pick/HorizonEffectiveIndex
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/HorizonEffectiveIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite strictly contractive Hankel matrices have a positive
   determinant index with singular-value, sum, normalization, and divergence laws. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * The atom ledger has empty `coverage_gids`, and its atom id occurs in no
     formalization receipt. Searches for horizon effective index, Hankel
     defect, singular-value determinant products, and orthogonal-sum laws in
     D5 found no owner. The three existing Weil/Pick modules and the nearby
     Cayley-Laguerre Chebyshev modules have different statements.
   * Pinned Mathlib supplies `Matrix.IsHermitian.charpoly_eq`,
     `Matrix.eval_charpoly`,
     `Matrix.eigenvalues_conjTranspose_mul_self_nonneg`,
     `Matrix.det_fromBlocks_zero₂₁`, `Matrix.isUnit_iff_isUnit_det`,
     `Real.log_inv`, and `tendsto_inv_nhdsGT_zero`. It does not package their
     combination as the effective-index theorem below.
   * Searches of the pinned non-Mathlib Lean packages found no theorem for
     this definition or its collection of laws. -/

noncomputable section

open scoped BigOperators Matrix Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Pick.HorizonEffectiveIndex

/-- A finite square matrix is Hankel when its entries are constant on finite
anti-diagonals. Its rank is automatically finite because its index type is
`Fin n`. -/
def IsFiniteHankel {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j k l, i.val + j.val = k.val + l.val → H i j = H k l

/-- The finite Hankel defect `I - Hᴴ H`. -/
def horizonDefect {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) : Matrix n n ℝ :=
  1 - Hᴴ * H

/-- The singular values of a finite real matrix, defined spectrally as the
nonnegative square roots of the eigenvalues of `Hᴴ H`. -/
def finiteSingularValue {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (i : n) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self H).eigenvalues i)

/-- Strict contraction in the finite singular-value formulation: every
singular value is strictly below one. -/
def IsStrictlyContractive {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) : Prop :=
  ∀ i, finiteSingularValue H i < 1

/-- The horizon effective index is the reciprocal determinant of the Hankel
defect. This is only an effective information index; no Jones-index
construction is asserted. -/
def horizonEffectiveIndex {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) : ℝ :=
  (horizonDefect H).det⁻¹

/-- Orthogonal direct sum of two finite matrices. -/
def orthogonalSum {m n : Type*}
    (H : Matrix m m ℝ) (K : Matrix n n ℝ) :
    Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  Matrix.fromBlocks H 0 0 K

lemma finiteSingularValue_sq {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (i : n) :
    finiteSingularValue H i ^ 2 =
      (Matrix.isHermitian_conjTranspose_mul_self H).eigenvalues i := by
  unfold finiteSingularValue
  exact Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg H i)

lemma horizonDefect_det_eq_prod {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) :
    (horizonDefect H).det =
      ∏ i, (1 - finiteSingularValue H i ^ 2) := by
  let hGram := Matrix.isHermitian_conjTranspose_mul_self H
  have hCharpoly :
      (Hᴴ * H).charpoly =
        ∏ i, (Polynomial.X - Polynomial.C (hGram.eigenvalues i)) := by
    simpa using hGram.charpoly_eq
  calc
    (horizonDefect H).det = (Hᴴ * H).charpoly.eval 1 := by
      rw [Matrix.eval_charpoly]
      simp [horizonDefect, Matrix.scalar]
    _ = (∏ i, (Polynomial.X -
          Polynomial.C (hGram.eigenvalues i))).eval 1 := by
      rw [hCharpoly]
    _ = ∏ i, (1 - finiteSingularValue H i ^ 2) := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp [finiteSingularValue_sq H]

lemma horizonDefect_orthogonalSum
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (H : Matrix m m ℝ) (K : Matrix n n ℝ) :
    horizonDefect (orthogonalSum H K) =
      Matrix.fromBlocks (horizonDefect H) 0 0 (horizonDefect K) := by
  unfold horizonDefect orthogonalSum
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply]

lemma horizonEffectiveIndex_orthogonalSum
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (H : Matrix m m ℝ) (K : Matrix n n ℝ) :
    horizonEffectiveIndex (orthogonalSum H K) =
      horizonEffectiveIndex H * horizonEffectiveIndex K := by
  simp [horizonEffectiveIndex, horizonDefect_orthogonalSum,
    Matrix.det_fromBlocks_zero₂₁, mul_comm]

lemma horizonEffectiveIndex_zero
    {n : Type*} [Fintype n] [DecidableEq n] :
    horizonEffectiveIndex (0 : Matrix n n ℝ) = 1 := by
  simp [horizonEffectiveIndex, horizonDefect]

/-- A singular factor diverges when its singular value approaches one from
below. -/
lemma singularFactor_tendsto_atTop :
    Filter.Tendsto (fun σ : ℝ ↦ (1 - σ ^ 2)⁻¹)
      (nhdsWithin 1 (Set.Iio 1)) Filter.atTop := by
  apply Filter.Tendsto.inv_tendsto_nhdsGT_zero
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have hContinuous : Continuous (fun σ : ℝ ↦ (1 : ℝ) - σ ^ 2) := by
      fun_prop
    convert! hContinuous.continuousWithinAt.tendsto <;> norm_num
  · filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with σ hσ
    change 0 < 1 - σ ^ 2
    rcases hσ with ⟨hLower, hUpper⟩
    nlinarith

lemma zero_isStrictlyContractive
    {n : Type*} [Fintype n] [DecidableEq n] :
    IsStrictlyContractive (0 : Matrix n n ℝ) := by
  let hZero := Matrix.isHermitian_conjTranspose_mul_self
    (0 : Matrix n n ℝ)
  have hEigen : hZero.eigenvalues = 0 :=
    hZero.eigenvalues_eq_zero_iff.mpr (by simp)
  intro i
  have hi := congrFun hEigen i
  change (Matrix.isHermitian_conjTranspose_mul_self
    (0 : Matrix n n ℝ)).eigenvalues i = 0 at hi
  change Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self
    (0 : Matrix n n ℝ)).eigenvalues i) < 1
  rw [hi]
  norm_num

/-- For every finite strictly contractive Hankel matrix, the defect is
invertible, its determinant and effective index are positive, and the index
has the determinant, logarithmic, and singular-value-product formulas. The
same definition is multiplicative on orthogonal sums, normalized at zero, and
its individual singular factor diverges at the contractive boundary. Finally,
the zero `1 × 1` Hankel matrix proves that the definition is inhabited. -/
theorem finite_hankel_horizon_effective_index :
    (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ),
        IsFiniteHankel H → IsStrictlyContractive H →
          IsUnit (horizonDefect H) ∧
          0 < (horizonDefect H).det ∧
          0 < horizonEffectiveIndex H ∧
          horizonEffectiveIndex H =
            ∏ i, (1 - finiteSingularValue H i ^ 2)⁻¹ ∧
          Real.log (horizonEffectiveIndex H) =
            -Real.log (horizonDefect H).det) ∧
      (∀ (m n : ℕ) (H : Matrix (Fin m) (Fin m) ℝ)
          (K : Matrix (Fin n) (Fin n) ℝ),
        horizonEffectiveIndex (orthogonalSum H K) =
          horizonEffectiveIndex H * horizonEffectiveIndex K) ∧
      (∀ n : ℕ, horizonEffectiveIndex
        (0 : Matrix (Fin n) (Fin n) ℝ) = 1) ∧
      Filter.Tendsto (fun σ : ℝ ↦ (1 - σ ^ 2)⁻¹)
        (nhdsWithin 1 (Set.Iio 1)) Filter.atTop ∧
      ∃ H : Matrix (Fin 1) (Fin 1) ℝ,
        IsFiniteHankel H ∧ IsStrictlyContractive H ∧
          horizonEffectiveIndex H = 1 := by
  refine ⟨?_, ?_, ?_, singularFactor_tendsto_atTop, ?_⟩
  · intro n H _ hContractive
    have hEigenLt :
        ∀ i, (Matrix.isHermitian_conjTranspose_mul_self H).eigenvalues i < 1 := by
      intro i
      have hNonneg : 0 ≤ finiteSingularValue H i :=
        Real.sqrt_nonneg _
      have hSquare := finiteSingularValue_sq H i
      have hLt := hContractive i
      nlinarith
    have hDetPos : 0 < (horizonDefect H).det := by
      rw [horizonDefect_det_eq_prod H]
      exact Finset.prod_pos fun i _ ↦ by
        rw [finiteSingularValue_sq H]
        exact sub_pos.mpr (hEigenLt i)
    have hDefectUnit : IsUnit (horizonDefect H) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr (ne_of_gt hDetPos)
    have hIndexPos : 0 < horizonEffectiveIndex H := by
      exact inv_pos.mpr hDetPos
    refine ⟨hDefectUnit, hDetPos, hIndexPos, ?_, ?_⟩
    · rw [horizonEffectiveIndex, horizonDefect_det_eq_prod H,
        ← Finset.prod_inv_distrib]
    · simp [horizonEffectiveIndex, Real.log_inv]
  · exact fun _ _ H K ↦ horizonEffectiveIndex_orthogonalSum H K
  · exact fun _ ↦ horizonEffectiveIndex_zero
  · refine ⟨0, ?_, zero_isStrictlyContractive, horizonEffectiveIndex_zero⟩
    intro i j k l _
    rfl

#print axioms finite_hankel_horizon_effective_index

end D5.S3.Weil.Pick.HorizonEffectiveIndex
