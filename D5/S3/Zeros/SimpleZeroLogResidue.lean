/- GID: D5/S3/Zeros/SimpleZeroLogResidue
   generality: G
   mirror-B: D5/B/S3/Zeros/SimpleZeroLogResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A simple analytic zero has unit normalized logarithmic residue. -/

import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.Basic

namespace D5.S3.Zeros.SimpleZeroLogResidue

open Filter Topology

/-- Mathlib-first wrapper for the local invariant behind the source atom's
full phase winding. At a simple analytic zero, multiplication by the
displacement removes the logarithmic derivative's simple pole and leaves
unit residue. -/
theorem simple_zero_has_unit_logarithmic_residue
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hzero : f z₀ = 0)
    (hderiv : deriv f z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) * logDeriv f z) (𝓝[≠] z₀) (𝓝 1) :=
  hf.tendsto_mul_logDeriv_simple_zero hzero hderiv

end D5.S3.Zeros.SimpleZeroLogResidue
