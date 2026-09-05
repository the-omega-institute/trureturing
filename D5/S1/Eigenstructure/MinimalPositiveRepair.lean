/- GID: D5/S1/Eigenstructure/MinimalPositiveRepair
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/MinimalPositiveRepair
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: The sharp positive repair of the Fibonacci eigenform, including the nonunique unrestricted equality case. -/

import D5.S1.Scale.FibonacciEigen
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Minimal positive repair

Library-search audit trail (2026-09-03):

* Six-way repository and in-flight branch searches found the frozen Fibonacci eigenpair theorem,
  but no positive-semidefinite repair theorem or equivalent operator-norm extremal statement.
* The spectral representative below directly uses the expanding and contracting eigenvalues proved
  in `D5.S1.Scale.FibonacciEigen`.
* Pinned Mathlib supplies `Matrix.PosSemidef.diagonal`, `Matrix.l2_opNorm_mulVec`,
  `Matrix.l2_opNorm_diagonal`, `PiLp.norm_apply_le`, and `Matrix.rank_diagonal`; no library theorem
  packages the complete sharp repair criterion.

The source's unrestricted uniqueness assertion is false: besides the negative-part repair,
`goldenRatio⁻¹ • I` is a distinct feasible repair with the same operator norm. The theorem records
that counterexample and states the valid uniqueness result for the coefficientwise least diagonal
repair in the Fibonacci eigenbasis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace D5.S1.Eigenstructure.MinimalPositiveRepair

/-- The Fibonacci substitution form in its expanding/contracting eigenbasis. -/
def fibonacciEigenform : Matrix (Fin 2) (Fin 2) Real :=
  Matrix.diagonal ![Real.goldenRatio, -Real.goldenRatio⁻¹]

/-- Projection onto the expanding Fibonacci eigendirection. -/
def expandingProjection : Matrix (Fin 2) (Fin 2) Real :=
  Matrix.diagonal ![1, 0]

/-- Projection onto the contracting Fibonacci eigendirection. -/
def contractingProjection : Matrix (Fin 2) (Fin 2) Real :=
  Matrix.diagonal ![0, 1]

/-- The negative-part repair, supported only on the contracting eigendirection. -/
def minimalRepair : Matrix (Fin 2) (Fin 2) Real :=
  Matrix.diagonal ![0, Real.goldenRatio⁻¹]

/-- A second sharp repair, showing that unrestricted equality is not unique. -/
def scalarRepair : Matrix (Fin 2) (Fin 2) Real :=
  Matrix.diagonal ![Real.goldenRatio⁻¹, Real.goldenRatio⁻¹]

/-- A repair is feasible when it and the repaired eigenform are positive semidefinite. -/
def FeasibleRepair (R : Matrix (Fin 2) (Fin 2) Real) : Prop :=
  R.PosSemidef ∧ (fibonacciEigenform + R).PosSemidef

/-- Spectral repairs are diagonal in the Fibonacci eigenbasis. -/
def SpectralRepair (R : Matrix (Fin 2) (Fin 2) Real) : Prop :=
  ∃ d : Fin 2 → Real, R = Matrix.diagonal d

/-- The valid uniqueness notion: coefficientwise least among feasible spectral repairs. -/
def IsLeastSpectralRepair (R : Matrix (Fin 2) (Fin 2) Real) : Prop :=
  FeasibleRepair R ∧ SpectralRepair R ∧
    ∀ S, FeasibleRepair S → SpectralRepair S → ∀ i, R i i ≤ S i i

private lemma diagonal_entry_nonneg {A : Matrix (Fin 2) (Fin 2) Real}
    (hA : A.PosSemidef) (i : Fin 2) : 0 ≤ A i i := by
  simpa using hA.2 (Finsupp.single i 1)

private lemma abs_entry_le_l2_opNorm (A : Matrix (Fin 2) (Fin 2) Real)
    (i j : Fin 2) : |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace Real (Fin 2) := PiLp.single 2 j 1
  calc
    |A i j| =
        ‖((EuclideanSpace.equiv (Fin 2) Real).symm (A *ᵥ e)) i‖ := by
          simp [e, Matrix.mulVec, Real.norm_eq_abs]
    _ ≤ ‖(EuclideanSpace.equiv (Fin 2) Real).symm (A *ᵥ e)‖ :=
      PiLp.norm_apply_le _ i
    _ ≤ ‖A‖ * ‖e‖ := A.l2_opNorm_mulVec e
    _ = ‖A‖ := by simp [e]

private lemma minimal_diagonal_le_of_feasible
    {R : Matrix (Fin 2) (Fin 2) Real} (hR : FeasibleRepair R) :
    ∀ i, minimalRepair i i ≤ R i i := by
  intro i
  fin_cases i
  · simpa [minimalRepair] using diagonal_entry_nonneg hR.1 (0 : Fin 2)
  · have h := diagonal_entry_nonneg hR.2 (1 : Fin 2)
    have hBound : Real.goldenRatio⁻¹ ≤ R 1 1 := by
      simpa [fibonacciEigenform, sub_eq_add_neg] using h
    simpa [minimalRepair] using hBound

private lemma repaired_form_diagonal :
    fibonacciEigenform + minimalRepair =
      Matrix.diagonal ![Real.goldenRatio, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibonacciEigenform, minimalRepair]

private lemma repaired_form :
    fibonacciEigenform + minimalRepair =
      Real.goldenRatio • expandingProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fibonacciEigenform, minimalRepair, expandingProjection]

private lemma minimal_repair_feasible : FeasibleRepair minimalRepair := by
  constructor
  · rw [minimalRepair, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · simp
    · exact inv_nonneg.mpr Real.goldenRatio_pos.le
  · rw [repaired_form_diagonal, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · simpa using Real.goldenRatio_pos.le
    · simp

private lemma scalar_repair_feasible : FeasibleRepair scalarRepair := by
  constructor
  · rw [scalarRepair, Matrix.posSemidef_diagonal_iff]
    rw [Fin.forall_fin_two]
    constructor
    · simpa only [Matrix.cons_val_zero] using
        (inv_nonneg.mpr Real.goldenRatio_pos.le)
    · simpa only [Matrix.cons_val_one, Matrix.cons_val_fin_one] using
        (inv_nonneg.mpr Real.goldenRatio_pos.le)
  · have hForm : fibonacciEigenform + scalarRepair =
        Matrix.diagonal ![Real.goldenRatio + Real.goldenRatio⁻¹, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [fibonacciEigenform, scalarRepair]
    rw [hForm, Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · exact add_nonneg Real.goldenRatio_pos.le
        (inv_nonneg.mpr Real.goldenRatio_pos.le)
    · simp

private lemma feasible_opNorm_lower_bound
    (R : Matrix (Fin 2) (Fin 2) Real) (hR : FeasibleRepair R) :
    Real.goldenRatio⁻¹ ≤ ‖R‖ := by
  have hEntry := minimal_diagonal_le_of_feasible hR (1 : Fin 2)
  have hToAbs : Real.goldenRatio⁻¹ ≤ |R 1 1| := by
    calc
      Real.goldenRatio⁻¹ = minimalRepair 1 1 := by simp [minimalRepair]
      _ ≤ R 1 1 := hEntry
      _ ≤ |R 1 1| := le_abs_self _
  exact hToAbs.trans (abs_entry_le_l2_opNorm R 1 1)

private lemma minimal_repair_opNorm_upper : ‖minimalRepair‖ ≤ Real.goldenRatio⁻¹ := by
  rw [minimalRepair, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg (inv_nonneg.mpr Real.goldenRatio_pos.le)]
  rw [Fin.forall_fin_two]
  constructor
  · simpa only [Matrix.cons_val_zero, norm_zero] using
      (inv_nonneg.mpr Real.goldenRatio_pos.le)
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr Real.goldenRatio_pos)]
    exact le_rfl

private lemma scalar_repair_opNorm_upper : ‖scalarRepair‖ ≤ Real.goldenRatio⁻¹ := by
  rw [scalarRepair, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg (inv_nonneg.mpr Real.goldenRatio_pos.le)]
  rw [Fin.forall_fin_two]
  constructor
  · simp only [Matrix.cons_val_zero, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr Real.goldenRatio_pos)]
    exact le_rfl
  · simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr Real.goldenRatio_pos)]
    exact le_rfl

private lemma scalar_repair_ne_minimal : scalarRepair ≠ minimalRepair := by
  intro hEq
  have hEntry := congrArg (fun A : Matrix (Fin 2) (Fin 2) Real => A 0 0) hEq
  have hZero : Real.goldenRatio⁻¹ = 0 := by
    simpa only [scalarRepair, minimalRepair, Matrix.diagonal_apply_eq,
      Matrix.cons_val_zero] using hEntry
  exact (inv_ne_zero Real.goldenRatio_ne_zero) hZero

private lemma least_spectral_repair_iff
    (R : Matrix (Fin 2) (Fin 2) Real) :
    IsLeastSpectralRepair R ↔ R = minimalRepair := by
  constructor
  · rintro ⟨hFeasible, ⟨d, hDiagonal⟩, hLeast⟩
    have hForward := minimal_diagonal_le_of_feasible hFeasible
    have hBackward := hLeast minimalRepair minimal_repair_feasible
      ⟨![0, Real.goldenRatio⁻¹], rfl⟩
    rw [hDiagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      exact le_antisymm (by simpa [hDiagonal] using hBackward i)
        (by simpa [hDiagonal] using hForward i)
    · simp [minimalRepair, Matrix.diagonal, hij]
  · intro hEq
    subst R
    exact ⟨minimal_repair_feasible, ⟨![0, Real.goldenRatio⁻¹], rfl⟩,
      fun _ hS _ => minimal_diagonal_le_of_feasible hS⟩

/--
Every feasible positive repair has L2 operator norm at least `goldenRatio⁻¹`. The negative-part
repair attains the bound and leaves the rank-one positive part. Equality is not unique among all
positive repairs, as the scalar repair witnesses. Uniqueness is restored precisely for the
coefficientwise least spectral repair.
-/
theorem minimal_positive_repair :
    (∀ R, FeasibleRepair R → Real.goldenRatio⁻¹ ≤ ‖R‖) ∧
      FeasibleRepair minimalRepair ∧
      ‖minimalRepair‖ = Real.goldenRatio⁻¹ ∧
      fibonacciEigenform + minimalRepair =
        Real.goldenRatio • expandingProjection ∧
      (fibonacciEigenform + minimalRepair).PosSemidef ∧
      (fibonacciEigenform + minimalRepair).rank = 1 ∧
      FeasibleRepair scalarRepair ∧
      ‖scalarRepair‖ = Real.goldenRatio⁻¹ ∧
      scalarRepair ≠ minimalRepair ∧
      ∀ R, IsLeastSpectralRepair R ↔ R = minimalRepair := by
  have hMinNorm : ‖minimalRepair‖ = Real.goldenRatio⁻¹ :=
    le_antisymm minimal_repair_opNorm_upper
      (feasible_opNorm_lower_bound minimalRepair minimal_repair_feasible)
  have hScalarNorm : ‖scalarRepair‖ = Real.goldenRatio⁻¹ :=
    le_antisymm scalar_repair_opNorm_upper
      (feasible_opNorm_lower_bound scalarRepair scalar_repair_feasible)
  have hRank : (fibonacciEigenform + minimalRepair).rank = 1 := by
    rw [repaired_form_diagonal, Matrix.rank_diagonal]
    let e : {i : Fin 2 // ![Real.goldenRatio, 0] i ≠ 0} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨0, by simpa using Real.goldenRatio_ne_zero⟩
        left_inv := by
          rintro ⟨i, hi⟩
          apply Subtype.ext
          fin_cases i
          · rfl
          · simp at hi
        right_inv := by intro x; cases x; rfl }
    simpa using Fintype.card_congr e
  exact ⟨feasible_opNorm_lower_bound, minimal_repair_feasible, hMinNorm,
    repaired_form, minimal_repair_feasible.2, hRank, scalar_repair_feasible,
    hScalarNorm, scalar_repair_ne_minimal, least_spectral_repair_iff⟩

#print axioms minimal_positive_repair

end D5.S1.Eigenstructure.MinimalPositiveRepair
