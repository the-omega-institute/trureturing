/- GID: D5/S3/QuantumChannels/ContractionSupremumOrder
   generality: G
   mirror-B: D5/B/S3/QuantumChannels/ContractionSupremumOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lift pointwise SLD-KM-RLD amplitude-damping order to open-axis suprema. -/

import D5.S3.QuantumChannels.ContractionSpectrumOrder

open Set
open D5.S3.QuantumChannels.AmplitudeDampingContraction
open D5.S3.QuantumChannels.ContractionSpectrumOrder

namespace D5.S3.QuantumChannels.ContractionSupremumOrder

/-!
# Amplitude-damping contraction supremum order

For fixed `gamma` in `[0,1)`, the pointwise SLD-KM-RLD ordering lifts to the indexed
suprema of the repository's scalar `coherenceRatio` model over `u ∈ (0,1)`.

This is only an ordering of those positive open-axis suprema. It does not establish an
all-state reduction and makes no claim about the negative axis.
-/

/-- The scalar amplitude-damping contraction-ratio suprema on `u ∈ (0,1)` satisfy
`SLD ≤ KM ≤ RLD`. -/
theorem contraction_supremum_order (gamma : ℝ)
    (hg0 : 0 ≤ gamma) (hg1 : gamma < 1) :
    (⨆ u : ↥(Ioo (0 : ℝ) 1),
        coherenceRatio sldRadialProfile gamma (u : ℝ)) ≤
      (⨆ u : ↥(Ioo (0 : ℝ) 1),
        coherenceRatio kmRadialProfile gamma (u : ℝ)) ∧
    (⨆ u : ↥(Ioo (0 : ℝ) 1),
        coherenceRatio kmRadialProfile gamma (u : ℝ)) ≤
      (⨆ u : ↥(Ioo (0 : ℝ) 1),
        coherenceRatio rldRadialProfile gamma (u : ℝ)) := by
  have hrld_bdd : BddAbove (Set.range (fun u : ↥(Ioo (0 : ℝ) 1) =>
      coherenceRatio rldRadialProfile gamma (u : ℝ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact (amplitude_damping_sld_rld_endpoints gamma hg0 hg1).2.1 (u : ℝ)
      ⟨by linarith [u.property.1], u.property.2⟩
  have hkm_bdd : BddAbove (Set.range (fun u : ↥(Ioo (0 : ℝ) 1) =>
      coherenceRatio kmRadialProfile gamma (u : ℝ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact (contraction_spectrum_order gamma (u : ℝ) hg0 hg1
      u.property.1 u.property.2).2.trans
        ((amplitude_damping_sld_rld_endpoints gamma hg0 hg1).2.1 (u : ℝ)
          ⟨by linarith [u.property.1], u.property.2⟩)
  constructor
  · exact ciSup_mono hkm_bdd fun u =>
      (contraction_spectrum_order gamma (u : ℝ) hg0 hg1
        u.property.1 u.property.2).1
  · exact ciSup_mono hrld_bdd fun u =>
      (contraction_spectrum_order gamma (u : ℝ) hg0 hg1
        u.property.1 u.property.2).2

end D5.S3.QuantumChannels.ContractionSupremumOrder
