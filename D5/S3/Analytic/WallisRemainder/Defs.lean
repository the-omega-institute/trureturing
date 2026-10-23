/- GID: D5/S3/Analytic/WallisRemainder/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/WallisRemainder/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: The Wallis gamma ratio and its three normalized remainder functions. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace D5.S3.Analytic.WallisRemainder.Defs

/-- The Wallis-type ratio √x Γ(x+1/2)/Γ(x+1). -/
noncomputable def wallisB (x : ℝ) : ℝ :=
  Real.sqrt x * Real.Gamma (x + 1/2) / Real.Gamma (x + 1)

noncomputable def mu (x : ℝ) : ℝ :=
  -x ^ 2 - ((3 / x) * (Real.log (wallisB x))⁻¹ + 24)⁻¹

noncomputable def theta (x : ℝ) : ℝ :=
  23040 * x ^ 5 / 31 * (3 * x / (24 * x ^ 2 + 1) + Real.log (wallisB x))

noncomputable def chi (x : ℝ) : ℝ :=
  358400 * x ^ 7 / 257 *
    ((120 * x ^ 2 + 31) / (96 * x * (10 * x ^ 2 + 3)) + Real.log (wallisB x))

/-- The open question, with the implicit well-definedness of the reciprocals in μ. -/
def claim : Prop :=
  (∀ x : ℝ, 0 < x → Real.log (wallisB x) ≠ 0 ∧
    (3 / x) * (Real.log (wallisB x))⁻¹ + 24 ≠ 0) ∧
  StrictMonoOn mu (Set.Ioi 0) ∧ StrictAntiOn theta (Set.Ioi 0) ∧
    StrictMonoOn chi (Set.Ioi 0)

end D5.S3.Analytic.WallisRemainder.Defs
