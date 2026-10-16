/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/RaySoundness
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: All original ray certificates imply their uniform Gram bound. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SparseRayCertificates
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.LeadingRayCertificates
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.TrailingRayCertificates
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.MiddleRayCertificates

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

set_option maxRecDepth 8192 in
theorem originalRay_valid (i : Fin 187) : (originalRay i).Valid := by
  by_cases h0 : i.val < 29
  · have hi : (⟨0 + (i.val - 0), by omega⟩ : Fin 187) = i := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simpa only [hi] using sparseRayCertificates ⟨i.val - 0, by omega⟩
  by_cases h1 : i.val < 92
  · have hi : (⟨29 + (i.val - 29), by omega⟩ : Fin 187) = i := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simpa only [hi] using leadingRayCertificates ⟨i.val - 29, by omega⟩
  by_cases h2 : i.val < 142
  · have hi : (⟨92 + (i.val - 92), by omega⟩ : Fin 187) = i := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simpa only [hi] using trailingRayCertificates ⟨i.val - 92, by omega⟩
  have hi : (⟨142 + (i.val - 142), by omega⟩ : Fin 187) = i := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  simpa only [hi] using middleRayCertificates ⟨i.val - 142, by omega⟩


theorem original_ray_gram_bound (i : Fin 187) (N j : ℕ)
    (hN : 67 ≤ N) (hl : 6 ≤ j) (hu : j ≤ N-10) :
    (∑ a, ∑ b, ((originalRay i).gap a : ℝ)*((originalRay i).gap b : ℝ)*
      (min (positions₁₆ N j a) (positions₁₆ N j b) : ℕ)) ≤
      bulkValue (N : ℝ) (bulkIndex N : ℝ)*
        (∑ a, ((originalRay i).gap a : ℝ)*(positions₁₆ N j a : ℝ))^2 := by
  exact ray_gram_bound (originalRay i) (originalRay_valid i) N j hN hl hu

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
