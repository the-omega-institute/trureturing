/- GID: D5/S3/Weil/Scattering/UniformDampingCriterion
   generality: I
   mirror-B: D5/B/S3/Weil/Scattering/UniformDampingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize uniform shifted-zero damping at the minimal height. -/

import D5.S3.Weil.ZeroSum

namespace D5.S3.Weil.Scattering.UniformDampingCriterion

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum

/-- At the minimal shift, the damping rate transported from a zero is its
real part.  Uniform rate one half is therefore equivalent to the critical-line
condition for every enumerated zero. -/
theorem uniform_damping_iff_critical_line (Z : ZeroData) :
    (∀ n, (Z.zero n).re = criticalAbscissa) ↔
      ∀ n, (1 / 2 : ℝ) + (Z.zero n).re - criticalAbscissa = 1 / 2 := by
  constructor
  · intro h n
    rw [h n]
    ring
  · intro h n
    have hn := h n
    rw [criticalAbscissa] at hn ⊢
    linarith

end D5.S3.Weil.Scattering.UniformDampingCriterion
