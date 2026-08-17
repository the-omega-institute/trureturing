/- GID: D5/S3/Analytic/Isolation/EntireZeroSetDichotomy
   generality: G
   mirror-B: D5/B/S3/Analytic/Isolation/EntireZeroSetDichotomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An entire function is identically zero or has a discrete zero set. -/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/- Provenance: thin wrapper over pinned mathlib's global isolated-zero theorem
   `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`. -/

namespace D5.S3.Analytic.Isolation.EntireZeroSetDichotomy

/-- An entire complex function either vanishes identically or has a discrete zero set. -/
theorem entire_zero_set_dichotomy (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) :
    f = 0 ∨ IsDiscrete (f ⁻¹' {0}) := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with hzero | hne
  · exact Or.inl ((Set.eqOn_univ f 0).mp hzero)
  · right
    have hcod : (f ⁻¹' {0})ᶜ ∈ Filter.codiscreteWithin Set.univ :=
      hne.mono fun _ hx ↦ by simpa using hx
    exact (compl_mem_codiscrete_iff.mp (by simpa [Filter.codiscrete] using hcod)).2

#print axioms entire_zero_set_dichotomy

end D5.S3.Analytic.Isolation.EntireZeroSetDichotomy
