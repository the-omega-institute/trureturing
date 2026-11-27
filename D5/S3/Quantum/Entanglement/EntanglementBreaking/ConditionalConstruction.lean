/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/ConditionalConstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/ConditionalConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Hermitian matrix and a PPT test give an indecomposable k-entanglement-breaking map. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.SchmidtCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open scoped ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

/-- Conditional matrix bridge for Devendra–Mallick–Sumesh, §7 Open Problem 1. -/
theorem conditional_indecomposable_kEB {k d : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hH : H.IsHermitian) (htr : H.trace = 0)
    (henergy : (d : ℝ)^4 / 2 ≤ (H * H).trace.re)
    (hQ : SchmidtQuadraticBound k H)
    (hR : (pptTest H).PosSemidef) (hΓ : (partialTranspose (pptTest H)).PosSemidef) :
    ∃ Φ : MatrixMap (Fin d) (Fin d) ℂ,
      inputChoi Φ = choiCandidate H ∧ IsKEB k Φ ∧ ¬ IsDecomposable Φ := by
  exact ⟨fromInputChoi (choiCandidate H), inputChoi_fromInputChoi _,
    candidate_isKEB hk hkd H hH hQ,
    candidate_indecomposable (hk.trans hkd) H htr henergy hR hΓ⟩

end D5.S3.Quantum.Entanglement.EntanglementBreaking
