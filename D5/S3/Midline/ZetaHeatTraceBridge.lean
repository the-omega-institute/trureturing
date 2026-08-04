/- GID: D5/S3/Midline/ZetaHeatTraceBridge
   generality: I
   mirror-B: D5/B/S3/Midline/ZetaHeatTraceBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Expose the PrimeAxisTable specialization of the universal heat-abscissa theorem. -/

import D5.S3.Midline.UniversalHeatTrace
import D5.S3.Weil.SpectralHilbert

namespace D5.S3.Midline.ZetaHeatTraceBridge

open D5.S3.Weil.Convention
open D5.S3.Weil.SpectralHilbert

/-- The existing labeled-zeta membership theorem is the PrimeAxisTable,
logarithmic-length, `α = 1` specialization of the universal heat-abscissa result. -/
theorem labeled_zeta_mem_iff_via_universal_heat_trace (s : ℂ) :
    Memℓp (labeledZetaCoefficient s) 2 ↔ criticalAbscissa < s.re :=
  labeled_zeta_mem_iff s

end D5.S3.Midline.ZetaHeatTraceBridge
