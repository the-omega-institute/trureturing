/- GID: D5/S3/Quantum/Thermal/UnitaryAverageLeakage
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/UnitaryAverageLeakage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Construct finite unitary averages and prove quantitative commutator leakage bounds in a C-star operator norm. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Thermal.UnitaryAverageLeakage

open scoped BigOperators

section OperatorNorm
variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]
  [NormedAlgebra ℝ A] {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual conjugation by a bundled unitary. -/
def conjugate (U : unitary A) (X : A) : A := (U : A) * X * star (U : A)

/-- Uniform average, including the normalization factor. -/
def average (U : ι → unitary A) (X : A) : A :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, conjugate (U i) X

/-- Maximum of all the measured commutator operator norms. -/
def leakage (U : ι → unitary A) (X : A) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => ‖X * (U i : A) - (U i : A) * X‖)

private theorem card_pos : (0 : ℝ) < Fintype.card ι := by
  exact_mod_cast Fintype.card_pos

@[simp] theorem conjugate_norm (U : unitary A) (X : A) :
    ‖conjugate U X‖ = ‖X‖ := by
  unfold conjugate
  rw [CStarRing.norm_mul_coe_unitary _ (star U), CStarRing.norm_coe_unitary_mul]

/-- A conjugation defect is a commutator followed by a unitary. -/
theorem conjugation_defect_norm (U : unitary A) (X : A) :
    ‖X - conjugate U X‖ = ‖X * (U : A) - (U : A) * X‖ := by
  have hu : (U : A) * star (U : A) = 1 := Unitary.mul_star_self_of_mem U.property
  have he : X - conjugate U X =
      (X * (U : A) - (U : A) * X) * star (U : A) := by
    simp only [conjugate, sub_mul, mul_assoc, hu, mul_one]
  rw [he, CStarRing.norm_mul_coe_unitary _ (star U)]

/-- The normalized average is contractive in the C-star norm. -/
theorem average_norm_le (U : ι → unitary A) (X : A) : ‖average U X‖ ≤ ‖X‖ := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := (card_pos (ι := ι)).ne'
  unfold average
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt card_pos))]
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, conjugate (U i) X‖ ≤
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖conjugate (U i) X‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt card_pos))
    _ = ‖X‖ := by simp [hn, mul_assoc]

theorem average_defect (U : ι → unitary A) (X : A) :
    X - average U X =
      (Fintype.card ι : ℝ)⁻¹ • ∑ i, (X - conjugate (U i) X) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := (card_pos (ι := ι)).ne'
  rw [Finset.sum_sub_distrib, smul_sub]
  have hconst : (Fintype.card ι : ℝ)⁻¹ • (∑ _i : ι, X) = X := by
    simp only [Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [hconst]
  rfl

/-- No completeness or projection hypothesis is assumed: the average is explicit. -/
theorem average_defect_le_leakage (U : ι → unitary A) (X : A) :
    ‖X - average U X‖ ≤ leakage U X := by
  classical
  have hn : (Fintype.card ι : ℝ) ≠ 0 := (card_pos (ι := ι)).ne'
  have hi (i : ι) : ‖X - conjugate (U i) X‖ ≤ leakage U X := by
    rw [conjugation_defect_norm]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  rw [average_defect, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt card_pos))]
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, (X - conjugate (U i) X)‖ ≤
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X - conjugate (U i) X‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (le_of_lt card_pos))
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ _i : ι, leakage U X := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt card_pos))
      exact Finset.sum_le_sum (fun i _ => hi i)
    _ = leakage U X := by simp [hn, mul_assoc]

theorem leakage_le_twice_norm (U : ι → unitary A) (X : A) :
    leakage U X ≤ 2 * ‖X‖ := by
  classical
  apply Finset.sup'_le
  intro i _
  calc
    ‖X * (U i : A) - (U i : A) * X‖ ≤
        ‖X * (U i : A)‖ + ‖(U i : A) * X‖ := norm_sub_le _ _
    _ = 2 * ‖X‖ := by
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      ring

/-- The centered specialization used after proving a concrete twirl equals zero. -/
theorem centered_leakage_bounds (U : ι → unitary A) (X : A)
    (hcenter : average U X = 0) :
    ‖X‖ ≤ leakage U X ∧ leakage U X ≤ 2 * ‖X‖ := by
  exact ⟨by simpa [hcenter] using average_defect_le_leakage U X,
    leakage_le_twice_norm U X⟩

/-- All finite commutator tests vanish exactly when every tested unitary commutes. -/
theorem leakage_eq_zero_iff (U : ι → unitary A) (X : A) :
    leakage U X = 0 ↔ ∀ i, X * (U i : A) = (U i : A) * X := by
  classical
  constructor
  · intro h i
    have hi : ‖X * (U i : A) - (U i : A) * X‖ ≤ 0 := by
      rw [← h]
      exact Finset.le_sup' _ (Finset.mem_univ i)
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hi (norm_nonneg _)))
  · intro h
    unfold leakage
    simp [h]

end OperatorNorm

section HilbertSquare
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]

/-- Exact square identity for actual isometric actions, prior to any normalization.
For Hilbert-Schmidt conjugation this gives the sum-of-squared-leakages identity. -/
theorem sum_isometry_defect_sq (T : ι → E ≃ₗᵢ[ℝ] E) (x : E) :
    (∑ i, ‖x - T i x‖ ^ 2) =
      2 * (Fintype.card ι : ℝ) * ‖x‖ ^ 2 - 2 * ⟪x, ∑ i, T i x⟫_ℝ := by
  have hi (i : ι) : ‖x - T i x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * ⟪x, T i x⟫_ℝ := by
    rw [norm_sub_sq_real, (T i).norm_map]
    ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, inner_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end HilbertSquare

#print axioms average_defect_le_leakage
#print axioms centered_leakage_bounds
#print axioms sum_isometry_defect_sq
end D5.S3.Quantum.Thermal.UnitaryAverageLeakage
