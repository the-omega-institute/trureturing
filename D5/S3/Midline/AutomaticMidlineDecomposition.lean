/- GID: D5/S3/Midline/AutomaticMidlineDecomposition
   generality: G
   mirror-B: D5/B/S3/Midline/AutomaticMidlineDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Half-density unitarity and self-resonance select the same automatic midline. -/

import D5.S3.Midline.UniversalHeatTrace

namespace D5.S3.Midline.AutomaticMidlineDecomposition

open D5.S3.Midline.UniversalHeatTrace

/-- Half-density unitarity and self-resonance are equivalent because each is
automatic exactly on the half-abscissa line. -/
theorem half_density_unitarity_iff_self_resonance
    {A : Type*} (M : A → ℝ) (α : ℝ)
    (hMnn : ∀ a, 0 ≤ M a) (hMne : ∃ a, M a ≠ 0)
    (s : ℂ) :
    (∀ a, ‖halfDensityCoefficient M α s a‖ = 1) ↔ KernelResonant α s s := by
  rw [half_density_unit_modulus_iff M α hMnn hMne s,
    (resonance_partner_spec α s s).2.1]

end D5.S3.Midline.AutomaticMidlineDecomposition
