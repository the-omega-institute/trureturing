/- GID: D5/S0/Diagonal/SechPath
   generality: G
   mirror-B: D5/B/S0/Diagonal/SechPath
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite step on a discrete hyperbolic-secant path stays strictly above zero. -/

import Mathlib

namespace D5.S0.Diagonal.SechPath

/-- The discrete hyperbolic-secant path never reaches the zero boundary. -/
theorem discrete_sech_path_positive (eta0 delta : ℝ) :
    ∀ k : ℕ, 0 < 1 / Real.cosh (eta0 + (k : ℝ) * delta) := by
  intro k
  exact one_div_pos.mpr (Real.cosh_pos _)

end D5.S0.Diagonal.SechPath
