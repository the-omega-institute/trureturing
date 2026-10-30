/- GID: D5/S3/Analytic/KilbasSaigo/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/KilbasSaigo/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-sided hyperbolic estimates for the Kilbas-Saigo function. -/

import D5.S3.Analytic.KilbasSaigo.Bounds

namespace D5.S3.Analytic.KilbasSaigo.Result
open D5.S3.Analytic.KilbasSaigo.Defs

/-- The pinned two-sided hyperbolic estimate. -/
theorem result : claim := by
  intro α m l x hα hαle hm hl hx
  exact Bounds.bounds hα hαle hm hl hx

end D5.S3.Analytic.KilbasSaigo.Result
