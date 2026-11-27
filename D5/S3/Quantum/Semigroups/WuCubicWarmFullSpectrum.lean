import D5.S3.Quantum.Semigroups.WuCubicConditionedRegion
import D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover

/-! The full-spectrum inequality for Wu v1, Remark 3.15 (3.54), at exponent
three with two equal-cap CAR modes and `1 ≤ r ≤ 6/5`. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Semigroups.WuCubicWarmFullSpectrum

open WuCubicOperatorBridge (Mat G)
open WuCubicAngularCertificate (physicalFrame)
open WuCubicOperatorNormalization
  (operatorDeficit operatorDeficit_zero operatorDeficit_scalar exists_ordered_normalization)
open WuCubicConditionedRegion (operatorDeficit_conditionedRegion_wider)
open WuCubicLowSpectrumCover (Tree root)
open private occupationBasis from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private levelsAt from D5.S3.Quantum.Semigroups.WuCubicSignedTransfer

private theorem physicalFrame_spectrum (U : unitary WuCubicDirectedOccupationCap.Mat)
    (v : Fin 4 → ℝ) :
    spectrum ℝ (physicalFrame U * diagonal (fun i => (v i : ℂ)) * (physicalFrame U)ᴴ) =
      Set.range v := by
  let D := diagonal (fun i => (v i : ℂ))
  let V := (U : WuCubicDirectedOccupationCap.Mat)
  have hreindex : physicalFrame U * D * (physicalFrame U)ᴴ =
      reindexAlgEquiv ℝ ℂ occupationBasis.symm (V * D * Vᴴ) := by
    change V.submatrix occupationBasis id * D * (V.submatrix occupationBasis id)ᴴ =
      (V * D * Vᴴ).submatrix occupationBasis occupationBasis
    rw [Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul _ _ occupationBasis id occupationBasis Function.bijective_id,
      Matrix.submatrix_mul _ _ occupationBasis id id Function.bijective_id,
      Matrix.submatrix_id_id]
  change spectrum ℝ (physicalFrame U * D * (physicalFrame U)ᴴ) = _
  rw [hreindex, AlgEquiv.spectrum_eq]
  refine (Unitary.spectrum_star_right_conjugate (R := ℝ) (U := U)).trans ?_
  ext a
  rw [← spectrum.algebraMap_mem_iff ℂ, spectrum_diagonal]
  change ((a : ℂ) ∈ Set.range (fun i => (v i : ℂ))) ↔ a ∈ Set.range v
  simp only [Set.mem_range, Complex.ofReal_inj]

/-- A positive-floor certificate on the closed low-spectrum box gives nonnegativity
for every positive semidefinite observable, with equality exactly at nonnegative scalars. -/
theorem operatorDeficit_nonneg_and_eq_zero_iff (tree : Tree) {floor : ℚ}
    (hfloor : 0 < floor) (hcheck : tree.check floor root = true)
    {r : ℝ} (hr : 1 ≤ r) (hrhi : r ≤ 6 / 5) {X : Mat} (hX : X.PosSemidef) :
    0 ≤ operatorDeficit r X ∧
      (operatorDeficit r X = 0 ↔ ∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : Mat)) := by
  rcases eq_or_ne X 0 with rfl | hX0
  · rw [operatorDeficit_zero]
    exact ⟨le_rfl, fun _ => ⟨0, le_rfl, by simp⟩, fun _ => rfl⟩
  obtain ⟨U, ell, m, n, q, hell, hmax, hm, hmn, hnq, hq, hM, hscale⟩ :=
    exists_ordered_normalization hr hX hX0
  have hscalar : (∃ c : ℝ, 0 ≤ c ∧ X = (c : ℂ) • (1 : Mat)) → operatorDeficit r X = 0 := by
    rintro ⟨c, _, rfl⟩
    exact operatorDeficit_scalar hr c
  by_cases hlow : m ≤ 63 / 100
  · have hbound := Tree.root_sound U tree hcheck ⟨hr, hrhi⟩ ⟨hm, hlow⟩ hmn hnq hq
    have hpos : 0 < operatorDeficit r X := by
      rw [hscale]
      exact mul_pos (pow_pos hell 3) ((Rat.cast_pos.mpr hfloor).trans_le hbound)
    exact ⟨hpos.le, fun h => (hpos.ne' h).elim, hscalar⟩
  · have hspec : spectrum ℝ (G r * X * G r) = Set.range (fun i => ell * levelsAt m n q i) := by
      rw [hM, physicalFrame_spectrum]
    have hmin : IsLeast (spectrum ℝ (G r * X * G r)) (ell * m) := by
      rw [hspec]
      refine ⟨⟨0, rfl⟩, ?_⟩
      rintro _ ⟨i, rfl⟩
      apply mul_le_mul_of_nonneg_left _ hell.le
      fin_cases i
      · exact le_rfl
      · exact hmn
      · exact hmn.trans hnq
      · exact hmn.trans (hnq.trans hq)
    have hratio : 63 / 100 * ell ≤ ell * m := by
      rw [mul_comm (63 / 100 : ℝ) ell]
      exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hlow)) hell.le
    obtain ⟨hnonneg, heq⟩ := operatorDeficit_conditionedRegion_wider hr hrhi hX hell hmax
      (fun _ ha => hratio.trans (hmin.2 ha))
    refine ⟨hnonneg, ?_, hscalar⟩
    intro h
    obtain ⟨c, hc, hXc⟩ := heq.mp h
    exact ⟨c, hc.le, hXc⟩

#print axioms operatorDeficit_nonneg_and_eq_zero_iff

end D5.S3.Quantum.Semigroups.WuCubicWarmFullSpectrum
