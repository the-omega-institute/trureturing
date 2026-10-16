/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound
   mirror-E: none(waiver:algebraic-spectrum-transfer)
   anchors: []
   utility: none
   digest: The rank-three length-twenty spectral relaxation has greatest purity seven over one hundred twenty-one. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.SpectralBoundaryTransfer
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN6PurityBound
import D5.S3.Quantum.Entanglement.AbsolutePPT.QutritN7PurityBound

set_option autoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
open Matrix SpectralBoundaryTransfer
open QutritSpectralReduction (K1 K2)

noncomputable section

private theorem endpoint_eighteen : SpectralBound 9 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 9 l = QutritSpectralReduction.boundaryValues 3 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex,
      QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  simpa [purityBound] using QutritN6PurityBound.certificate_bound l ho (hn 17) ht h1 h2

private theorem endpoint_twenty_one : SpectralBound 12 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 12 l = QutritSpectralReduction.boundaryValues 4 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex,
      QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  simpa [purityBound] using QutritN7PurityBound.certificate_bound l ho (hn 20) ht h1 h2

private theorem intermediate_nineteen : SpectralBound 10 :=
  spectral_bound_transfer 9 2 (by decide) endpoint_eighteen endpoint_twenty_one

/- proof_shape: spectral_purity_bound: bind-only
   consumer: sharp_spectral_purity_bound
   escape_witness: none -/
theorem spectral_purity_bound (l : Fin 20 → ℝ) (ho : Antitone l)
    (hn : ∀ i, 0 ≤ l i) (ht : ∑ i, l i = 1)
    (h1 : (K1 (boundaryValues 11 l)).PosSemidef)
    (h2 : (K2 (boundaryValues 11 l)).PosSemidef) :
    ∑ i, (l i) ^ 2 ≤ (7 : ℝ) / 121 := by
  have htwenty : SpectralBound 11 :=
    spectral_bound_transfer 10 1 (by decide) intermediate_nineteen endpoint_twenty_one
  simpa [purityBound] using htwenty l ho hn ht h1 h2

private def equalitySpectrum : Fin 20 → ℝ := fun i => if i = 0 then 3 / 22 else 1 / 22

private theorem equality_order : Antitone equalitySpectrum := by
  intro i j hij
  by_cases hj : j = 0
  · have hi : i = 0 := by
      subst j
      apply Fin.ext
      change i.val = 0
      change i.val ≤ 0 at hij
      omega
    simp [hi, hj]
  · by_cases hi : i = 0
    · norm_num [equalitySpectrum, hi, hj]
    · simp [equalitySpectrum, hi, hj]

private theorem equality_K1 : (K1 (boundaryValues 11 equalitySpectrum)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, K1, boundaryValues, boundaryIndex, equalitySpectrum]
  · intro x
    norm_num [K1, boundaryValues, boundaryIndex, equalitySpectrum,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 2)]

private theorem equality_K2 : (K2 (boundaryValues 11 equalitySpectrum)).PosSemidef := by
  have heq : K2 (boundaryValues 11 equalitySpectrum) =
      K1 (boundaryValues 11 equalitySpectrum) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [K1, K2, boundaryValues, boundaryIndex, equalitySpectrum]
  rw [heq]
  exact equality_K1

/- proof_shape: sharp_spectral_purity_bound: content
   escape_witness: the explicit ordered spectrum has mass one, both actual
     boundary matrices positive semidefinite and square sum exactly 7/121.
   admission_basis: escape-witness -/
/-- Sharpness is asserted for the rank-three spectral relaxation only. -/
theorem sharp_spectral_purity_bound : IsGreatest
    {p : ℝ | ∃ l : Fin 20 → ℝ, Antitone l ∧ (∀ i, 0 ≤ l i) ∧
      (∑ i, l i) = 1 ∧ (K1 (boundaryValues 11 l)).PosSemidef ∧
      (K2 (boundaryValues 11 l)).PosSemidef ∧ (∑ i, (l i) ^ 2) = p}
    (7 / 121 : ℝ) := by
  constructor
  · refine ⟨equalitySpectrum, equality_order, ?_, ?_, equality_K1, equality_K2, ?_⟩
    · intro i
      dsimp [equalitySpectrum]
      split_ifs <;> norm_num
    · norm_num [equalitySpectrum, Fin.sum_univ_succ]
    · norm_num [equalitySpectrum, Fin.sum_univ_succ]
  · intro p hp
    obtain ⟨l, ho, hn, ht, h1, h2, rfl⟩ := hp
    exact spectral_purity_bound l ho hn ht h1 h2

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
