/- GID: D5/S3/Analytic/GaussZeroBalanced/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two sharp classifications for the zero-balanced Gauss quotient. -/

import D5.S3.Analytic.GaussZeroBalanced.ParamDeriv
import D5.S3.Analytic.GaussZeroBalanced.Comparison

namespace D5.S3.Analytic.GaussZeroBalanced.Result

open D5.S3.Analytic.GaussZeroBalanced.Defs

/-- The sharp parameter classifications of the zero-balanced Gauss quotient. -/
theorem result : claim := ⟨ParamDeriv.clause1, Comparison.clause2⟩

end D5.S3.Analytic.GaussZeroBalanced.Result
