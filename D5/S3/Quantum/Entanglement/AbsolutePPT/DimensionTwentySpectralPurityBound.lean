/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/DimensionTwentySpectralPurityBound
   mirror-E: none(waiver:algebraic-spectrum-transfer)
   anchors: []
   utility: none
   digest: The rank-three length-twenty spectral relaxation has purity at most seven over one hundred twenty-one. -/

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
  convert QutritN6PurityBound.certificate_bound l ho (hn 17) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem endpoint_twenty_one : SpectralBound 12 := by
  intro l ho hn ht h1 h2
  have hb : boundaryValues 12 l = QutritSpectralReduction.boundaryValues 4 l := by
    funext q
    fin_cases q <;> norm_num [boundaryValues, boundaryIndex,
      QutritSpectralReduction.boundaryValues]
  rw [hb] at h1 h2
  convert QutritN7PurityBound.certificate_bound l ho (hn 20) ht h1 h2 using 1 <;>
    norm_num [purityBound]

private theorem intermediate_nineteen : SpectralBound 10 :=
  spectral_bound_transfer 9 2 (by decide) endpoint_eighteen endpoint_twenty_one

/- proof_shape: spectral_purity_bound: content after expansion through the
   same-delivery new spectral_bound_transfer, including its actual-pivot
   insertion/deletion and positive normalization. The endpoint_eighteen
   and endpoint_twenty_one helpers only adapt baseline-frozen certificates;
   intermediate_nineteen uses the new transfer on the live proof path.
   consumer: QuadbitQuintitMaximumPurity.density_bound
   escape_witness: SpectralBoundaryTransfer.spectral_bound_transfer
   admission_basis: escape-witness
   utility:none rationale: This universal inequality uses symbolic structural
   transfer. It introduces no new finite equality certificate, enumeration,
   coefficient object or checker. The length-21 source change only exposes
   the original private baseline certificate. -/
theorem spectral_purity_bound (l : Fin 20 → ℝ) (ho : Antitone l)
    (hn : ∀ i, 0 ≤ l i) (ht : ∑ i, l i = 1)
    (h1 : (K1 (boundaryValues 11 l)).PosSemidef)
    (h2 : (K2 (boundaryValues 11 l)).PosSemidef) :
    ∑ i, (l i) ^ 2 ≤ (7 : ℝ) / 121 := by
  have htwenty : SpectralBound 11 :=
    spectral_bound_transfer 10 1 (by decide) intermediate_nineteen endpoint_twenty_one
  convert htwenty l ho hn ht h1 h2 using 1 <;> norm_num [purityBound]

#print axioms spectral_purity_bound
#print axioms QutritN7PurityBound.certificate_bound

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.DimensionTwentySpectralPurityBound
