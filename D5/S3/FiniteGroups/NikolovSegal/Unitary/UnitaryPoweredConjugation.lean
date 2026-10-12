/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPoweredConjugation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryPoweredConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryDiagonalGeometry

namespace NikolovSegal.UnitaryField
open Matrix
variable {F : Type*} [Field F] [Finite F]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem diagonalSL_pow_val (w : I → Fˣ) (hw : ∏ i, w i = 1) (s : ℕ) :
    ((diagonalSL w hw)^s).val = diagonal (fun i => (((w i)^s : Fˣ) : F)) := by
  induction s with
  | zero =>
    rw [pow_zero]
    change (1 : Matrix I I F) = diagonal _
    simp
  | succ s ih =>
    rw [pow_succ, SpecialLinearGroup.coe_mul, ih]
    change diagonal (fun i => ((w i)^s : F)) * diagonal (fun i => (w i : F)) = _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp [pow_succ]

theorem diagonalSL_pow_inv_val (w : I → Fˣ) (hw : ∏ i, w i = 1) (s : ℕ) :
    (((diagonalSL w hw)^s)⁻¹).val = diagonal (fun i => ((((w i)^s)⁻¹ : Fˣ) : F)) := by
  have hprod : ∏ i, ((w i)^s)⁻¹ = 1 := by
    rw [Finset.prod_inv_distrib, Finset.prod_pow, hw]
    simp
  let v := diagonalSL (fun i => ((w i)^s)⁻¹) hprod
  have hmul : (diagonalSL w hw)^s * v = 1 := by
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, diagonalSL_pow_val]
    change diagonal _ * diagonal _ = (1 : Matrix I I F)
    rw [diagonal_mul_diagonal]
    simp
  have hv : v = ((diagonalSL w hw)^s)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [← hv]
  rfl

theorem actual_powered_conjugation (w : I → Fˣ) (hw : ∏ i, w i = 1)
    (s : ℕ) (A : SpecialLinearGroup I F) (r c : I) :
    (((diagonalSL w hw)^s * A * ((diagonalSL w hw)^s)⁻¹).val) r c =
      (((w r / w c)^s : Fˣ) : F) * A.val r c := by
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
    diagonalSL_pow_val, diagonalSL_pow_inv_val, diagonal_conjugation_entries]
  rw [div_pow]

theorem actual_powered_transvection (w : I → Fˣ) (hw : ∏ i, w i = 1)
    (s : ℕ) {r c : I} (hrc : r ≠ c) (t : F) :
    (diagonalSL w hw)^s * SpecialLinearGroup.transvection hrc t *
      ((diagonalSL w hw)^s)⁻¹ =
      SpecialLinearGroup.transvection hrc ((((w r / w c)^s : Fˣ) : F) * t) := by
  apply Subtype.ext
  ext i j
  rw [actual_powered_conjugation]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply]
  by_cases hij : i = j
  · subst j
    have hboth : ¬(r = i ∧ c = i) := fun h => hrc (h.1.trans h.2.symm)
    simp [Matrix.single, hboth]
  · by_cases hi : i = r
    · subst i
      by_cases hj : j = c
      · subst j; simp [Matrix.single, hrc]
      · simp [Matrix.single, hij, hj, Ne.symm hj]
    · simp [Matrix.single, hij, hi, Ne.symm hi]

end NikolovSegal.UnitaryField
