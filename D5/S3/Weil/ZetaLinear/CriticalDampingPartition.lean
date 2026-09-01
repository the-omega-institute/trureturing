/- GID: D5/S3/Weil/ZetaLinear/CriticalDampingPartition
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaLinear/CriticalDampingPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Relate finite diagonal damping, centered defects, and the symmetric partition trace. -/

import D5.S3.Zeros.Symmetry.CriticalDampingFlatness
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaLinear.CriticalDampingPartition

open D5.S3.Zeros.Symmetry.CriticalDampingFlatness
open scoped BigOperators

attribute [local instance] Matrix.normedAddCommGroup

/-! ## Finite damping operators and their centered defects -/

/-- The complex diagonal damping operator attached to a finite family of real rates. -/
def dampingOperator {n : ℕ} (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i ↦ (d i : ℂ)

/-- The pointwise defect of a damping rate from a prescribed center. -/
def centeredDampingDefect {n : ℕ} (d : Fin n → ℝ) (c : ℝ) (i : Fin n) : ℝ :=
  d i - c

/-- The damping operator after subtracting the scalar center. -/
def centeredDampingOperator {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  dampingOperator d - (c : ℂ) • 1

theorem centered_damping_operator_eq_diagonal {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    centeredDampingOperator d c =
      Matrix.diagonal (fun i ↦ ((centeredDampingDefect d c i : ℝ) : ℂ)) := by
  rw [centeredDampingOperator, dampingOperator, Matrix.smul_one_eq_diagonal,
    Matrix.diagonal_sub]
  congr 1
  funext i
  simp [centeredDampingDefect]

/-- A diagonal damping operator is scalar exactly when every rate equals the scalar center. -/
theorem damping_operator_eq_scalar_iff {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    dampingOperator d = (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ↔
      ∀ i, d i = c := by
  rw [dampingOperator, Matrix.smul_one_eq_diagonal, Matrix.diagonal_eq_diagonal_iff]
  constructor
  · intro h i
    exact_mod_cast h i
  · intro h i
    exact_mod_cast h i

/-- Pointwise vanishing of the centered defect is the scalar damping condition. -/
theorem centered_damping_defect_zero_iff {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    (∀ i, centeredDampingDefect d c i = 0) ↔ ∀ i, d i = c := by
  simp only [centeredDampingDefect, sub_eq_zero]

/-- A witness that the universal finset is nonempty when the window dimension is positive. -/
def fin_univ_nonempty {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The matrix sup norm of the centered diagonal operator is the largest centered rate. -/
theorem centered_damping_operator_norm_eq_sup {n : ℕ} (d : Fin n → ℝ) (c : ℝ)
    (hn : 0 < n) :
    ‖centeredDampingOperator d c‖ =
      Finset.univ.sup' (fin_univ_nonempty hn) (fun i ↦ |d i - c|) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [centered_damping_operator_eq_diagonal, Matrix.norm_diagonal]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonempty]
    intro i
    change ‖((d i - c : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact Finset.le_sup' (f := fun j : Fin n ↦ |d j - c|) (Finset.mem_univ i)
  · refine Finset.sup'_le _ _ fun i _ ↦ ?_
    calc
      |d i - c| = ‖((d i - c : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖((centeredDampingDefect d c i : ℝ) : ℂ)‖ := by
        rw [centeredDampingDefect]
      _ ≤ ‖fun j : Fin n ↦ ((centeredDampingDefect d c j : ℝ) : ℂ)‖ :=
        norm_le_pi_norm (fun j : Fin n ↦ ((centeredDampingDefect d c j : ℝ) : ℂ)) i

/-- The same finite maximum expresses uniform boundedness of all centered rates. -/
theorem centered_damping_bound_iff_sup_le {n : ℕ} (d : Fin n → ℝ) (c ε : ℝ)
    (hn : 0 < n) :
    (∀ i, |d i - c| ≤ ε) ↔
      Finset.univ.sup' (fin_univ_nonempty hn) (fun i ↦ |d i - c|) ≤ ε := by
  rw [Finset.sup'_le_iff]
  simp only [Finset.mem_univ, forall_const]

/-- The critical-line statement for a finite family of complex zero parameters. -/
theorem finite_zero_critical_line_iff_defect_zero {n : ℕ} (zeros : Fin n → ℂ) :
    (∀ i, (zeros i).re = 1 / 2) ↔
      ∀ i, centeredDampingDefect (fun j ↦ (zeros j).re) (1 / 2) i = 0 := by
  exact (centered_damping_defect_zero_iff (fun j ↦ (zeros j).re) (1 / 2)).symm

/-! ## Partition traces -/

/-- The normalized real damping partition function from (349.3). -/
def dampingPartition {n : ℕ} (d : Fin n → ℝ) (tau : ℝ) : ℝ :=
  Real.exp (tau / 2) * ∑ i, Real.exp (-tau * d i)

/-- Reflection stability of the multiset of centered rates, witnessed by a permutation. -/
def CenteredSpectrumSymmetric {n : ℕ} (d : Fin n → ℝ) (c : ℝ) : Prop :=
  ∃ sigma : Equiv.Perm (Fin n), ∀ i, d (sigma i) - c = -(d i - c)

/-- Matrix hyperbolic cosine, defined through the matrix exponential. -/
def matrixCosh {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2 : ℂ)⁻¹ • (NormedSpace.exp A + NormedSpace.exp (-A))

/-- The partition defect from (349.5). -/
def criticalDampingPartitionDefect {n : ℕ} (d : Fin n → ℝ) (tau : ℝ) : ℝ :=
  dampingPartition d tau - n

theorem damping_partition_eq_centered_sum {n : ℕ} (d : Fin n → ℝ) (tau : ℝ) :
    dampingPartition d tau =
      ∑ i, Real.exp (-tau * (d i - 1 / 2)) := by
  rw [dampingPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.exp_add]
  congr 1
  ring

theorem damping_exponential_trace_eq_sum {n : ℕ} (d : Fin n → ℝ) (tau : ℝ) :
    Matrix.trace (NormedSpace.exp ((-tau : ℂ) • dampingOperator d)) =
      ((∑ i, Real.exp (-tau * d i) : ℝ) : ℂ) := by
  rw [dampingOperator, ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.trace_diagonal]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  congr 1

theorem damping_partition_eq_matrix_trace {n : ℕ} (d : Fin n → ℝ) (tau : ℝ) :
    (dampingPartition d tau : ℂ) =
      Complex.exp (tau / 2 : ℂ) *
        Matrix.trace (NormedSpace.exp ((-tau : ℂ) • dampingOperator d)) := by
  rw [dampingPartition, damping_exponential_trace_eq_sum]
  push_cast
  rfl

theorem centered_exponential_trace_eq_sum {n : ℕ} (d : Fin n → ℝ) (c tau : ℝ) :
    Matrix.trace (NormedSpace.exp ((-tau : ℂ) • centeredDampingOperator d c)) =
      ((∑ i, Real.exp (-tau * (d i - c)) : ℝ) : ℂ) := by
  rw [centered_damping_operator_eq_diagonal, ← Matrix.diagonal_smul,
    Matrix.exp_diagonal, Matrix.trace_diagonal]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  congr 1
  simp [centeredDampingDefect, smul_eq_mul]

theorem damping_partition_eq_centered_trace {n : ℕ} (d : Fin n → ℝ) (tau : ℝ) :
    (dampingPartition d tau : ℂ) =
      Matrix.trace
        (NormedSpace.exp ((-tau : ℂ) • centeredDampingOperator d (1 / 2))) := by
  rw [damping_partition_eq_centered_sum, centered_exponential_trace_eq_sum]

theorem matrix_cosh_diagonal {n : ℕ} (v : Fin n → ℂ) :
    matrixCosh (Matrix.diagonal v) = Matrix.diagonal (fun i ↦ Complex.cosh (v i)) := by
  rw [matrixCosh, Matrix.exp_diagonal, Matrix.diagonal_neg, Matrix.exp_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.cosh, div_eq_mul_inv,
      mul_comm]
  · simp [hij]

theorem centered_cosh_trace_eq_sum {n : ℕ} (d : Fin n → ℝ) (c tau : ℝ) :
    Matrix.trace (matrixCosh ((tau : ℂ) • centeredDampingOperator d c)) =
      ((∑ i, Real.cosh (tau * (d i - c)) : ℝ) : ℂ) := by
  rw [centered_damping_operator_eq_diagonal, ← Matrix.diagonal_smul,
    matrix_cosh_diagonal, Matrix.trace_diagonal]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp [centeredDampingDefect]

theorem centered_exponential_sum_eq_cosh_sum {n : ℕ} (d : Fin n → ℝ) (c tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d c) :
    (∑ i, Real.exp (-tau * (d i - c))) =
      ∑ i, Real.cosh (tau * (d i - c)) := by
  rcases hsym with ⟨sigma, hsigma⟩
  have hpositive :
      (∑ i, Real.exp (tau * (d i - c))) =
        ∑ i, Real.exp (-tau * (d i - c)) := by
    calc
      (∑ i, Real.exp (tau * (d i - c))) =
          ∑ i, Real.exp (tau * (d (sigma i) - c)) :=
        (Equiv.sum_comp sigma (fun i ↦ Real.exp (tau * (d i - c)))).symm
      _ = ∑ i, Real.exp (-tau * (d i - c)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsigma]
        congr 1
        ring
  rw [show (∑ i, Real.cosh (tau * (d i - c))) =
      ((∑ i, Real.exp (tau * (d i - c))) +
        ∑ i, Real.exp (-tau * (d i - c))) / 2 by
      simp_rw [Real.cosh_eq]
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring]
  rw [hpositive]
  ring

theorem damping_partition_eq_cosh_sum {n : ℕ} (d : Fin n → ℝ) (tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d (1 / 2)) :
    dampingPartition d tau = ∑ i, Real.cosh (tau * (d i - 1 / 2)) := by
  rw [damping_partition_eq_centered_sum]
  exact centered_exponential_sum_eq_cosh_sum d (1 / 2) tau hsym

theorem damping_partition_eq_cosh_trace {n : ℕ} (d : Fin n → ℝ) (tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d (1 / 2)) :
    (dampingPartition d tau : ℂ) =
      Matrix.trace (matrixCosh ((tau : ℂ) • centeredDampingOperator d (1 / 2))) := by
  rw [damping_partition_eq_cosh_sum d tau hsym, centered_cosh_trace_eq_sum]

theorem partition_defect_eq_finite_cosh_defect {n : ℕ} (d : Fin n → ℝ) (tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d (1 / 2)) :
    criticalDampingPartitionDefect d tau = criticalDampingDefect d tau := by
  rw [criticalDampingPartitionDefect, damping_partition_eq_cosh_sum d tau hsym]
  simp [criticalDampingDefect, Finset.sum_sub_distrib]

theorem critical_damping_partition_defect_nonneg {n : ℕ} (d : Fin n → ℝ) (tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d (1 / 2)) :
    0 ≤ criticalDampingPartitionDefect d tau := by
  rw [partition_defect_eq_finite_cosh_defect d tau hsym, criticalDampingDefect]
  exact Finset.sum_nonneg fun i _ ↦ sub_nonneg.mpr (Real.one_le_cosh _)

theorem critical_line_iff_partition_defect_zero {n : ℕ} (d : Fin n → ℝ) (tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d (1 / 2)) (htau : tau ≠ 0) :
    (∀ i, d i = 1 / 2) ↔ criticalDampingPartitionDefect d tau = 0 := by
  rw [partition_defect_eq_finite_cosh_defect d tau hsym]
  exact critical_damping_flatness_criterion d tau htau

/-- Formulas (349.3)--(349.6), together with their nonzero-scale vanishing criterion. -/
theorem critical_damping_partition_certificate {n : ℕ} (d : Fin n → ℝ) (tau : ℝ)
    (hsym : CenteredSpectrumSymmetric d (1 / 2)) (htau : tau ≠ 0) :
    (dampingPartition d tau : ℂ) =
        Complex.exp (tau / 2 : ℂ) *
          Matrix.trace (NormedSpace.exp ((-tau : ℂ) • dampingOperator d)) ∧
      (dampingPartition d tau : ℂ) =
        Matrix.trace
          (NormedSpace.exp ((-tau : ℂ) • centeredDampingOperator d (1 / 2))) ∧
      (dampingPartition d tau : ℂ) =
        Matrix.trace (matrixCosh ((tau : ℂ) • centeredDampingOperator d (1 / 2))) ∧
      0 ≤ criticalDampingPartitionDefect d tau ∧
      ((∀ i, d i = 1 / 2) ↔ criticalDampingPartitionDefect d tau = 0) := by
  exact ⟨damping_partition_eq_matrix_trace d tau,
    damping_partition_eq_centered_trace d tau,
    damping_partition_eq_cosh_trace d tau hsym,
    critical_damping_partition_defect_nonneg d tau hsym,
    critical_line_iff_partition_defect_zero d tau hsym htau⟩

/-! ## Concrete nonempty witnesses -/

def criticalThreePointRates : Fin 3 → ℝ :=
  ![1 / 2, 1 / 2, 1 / 2]

def offlineThreePointRates : Fin 3 → ℝ :=
  ![1 / 2, 3 / 4, 1 / 2]

theorem critical_three_point_certificate :
    (∀ i, centeredDampingDefect criticalThreePointRates (1 / 2) i = 0) ∧
      dampingOperator criticalThreePointRates =
        ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  constructor
  · intro i
    fin_cases i <;> norm_num [centeredDampingDefect, criticalThreePointRates]
  · rw [damping_operator_eq_scalar_iff]
    intro i
    fin_cases i <;> norm_num [criticalThreePointRates]

theorem offline_three_point_certificate :
    centeredDampingDefect offlineThreePointRates (1 / 2) (1 : Fin 3) = 1 / 4 ∧
      Finset.univ.sup' (fin_univ_nonempty (by norm_num : 0 < 3))
          (fun i ↦ |offlineThreePointRates i - 1 / 2|) = 1 / 4 ∧
      dampingOperator offlineThreePointRates ≠
        ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  constructor
  · norm_num [centeredDampingDefect, offlineThreePointRates]
  constructor
  · apply le_antisymm
    · refine Finset.sup'_le _ _ fun i _ ↦ ?_
      fin_cases i <;> norm_num [offlineThreePointRates]
    · exact Finset.le_sup'_of_le
        (f := fun i : Fin 3 ↦ |offlineThreePointRates i - 1 / 2|)
        (Finset.mem_univ (1 : Fin 3))
        (by norm_num [offlineThreePointRates])
  · intro hscalar
    have hall := (damping_operator_eq_scalar_iff offlineThreePointRates (1 / 2)).mp hscalar
    have hoffline := hall (1 : Fin 3)
    norm_num [offlineThreePointRates] at hoffline

/- Contract examples restate the public surface exercised above. -/

example {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    dampingOperator d = (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) ↔
      ∀ i, d i = c :=
  damping_operator_eq_scalar_iff d c

example {n : ℕ} (d : Fin n → ℝ) (c : ℝ) :
    (∀ i, centeredDampingDefect d c i = 0) ↔ ∀ i, d i = c :=
  centered_damping_defect_zero_iff d c

example {n : ℕ} (d : Fin n → ℝ) (c : ℝ) (hn : 0 < n) :
    ‖centeredDampingOperator d c‖ =
      Finset.univ.sup' (fin_univ_nonempty hn) (fun i ↦ |d i - c|) :=
  centered_damping_operator_norm_eq_sup d c hn

example {n : ℕ} (zeros : Fin n → ℂ) :
    (∀ i, (zeros i).re = 1 / 2) ↔
      ∀ i, centeredDampingDefect (fun j ↦ (zeros j).re) (1 / 2) i = 0 :=
  finite_zero_critical_line_iff_defect_zero zeros

example :
    (∀ i, centeredDampingDefect criticalThreePointRates (1 / 2) i = 0) ∧
      dampingOperator criticalThreePointRates =
        ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  critical_three_point_certificate

example :
    centeredDampingDefect offlineThreePointRates (1 / 2) (1 : Fin 3) = 1 / 4 ∧
      Finset.univ.sup' (fin_univ_nonempty (by norm_num : 0 < 3))
          (fun i ↦ |offlineThreePointRates i - 1 / 2|) = 1 / 4 ∧
      dampingOperator offlineThreePointRates ≠
        ((1 / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  offline_three_point_certificate

#print axioms critical_damping_partition_certificate
#print axioms critical_three_point_certificate
#print axioms offline_three_point_certificate

end D5.S3.Weil.ZetaLinear.CriticalDampingPartition
