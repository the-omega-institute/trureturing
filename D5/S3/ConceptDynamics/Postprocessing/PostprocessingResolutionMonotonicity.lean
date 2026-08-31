/- GID: D5/S3/ConceptDynamics/Postprocessing/PostprocessingResolutionMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Postprocessing/PostprocessingResolutionMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Deterministic postprocessing cannot refine an identification kernel. -/

import D5.S3.ConceptDynamics.Postprocessing.PostprocessingKernelMonotonicity

/- Library-search audit trail (2026-09-01):
   * The five-route D5 search found the exact general theorem
     `postprocessing_kernel_mono` in the imported module. This declaration is
     therefore a thin atom-specific wrapper rather than a second proof.
   * The same-section identification criterion remains residual-open, while
     `LanguagePostprocessingObstruction` is a witness-level consequence of the
     imported kernel inclusion and has a less general conclusion.
   * Pinned Mathlib source searches found `Setoid.ker` and its quotient and
     injectivity API, but no composition-inclusion theorem. A Loogle query for
     `Setoid.ker f ≤ Setoid.ker (g ∘ f)` returned no hit; the LeanSearch
     endpoint was unavailable. The ordered search stopped at the exact D5 hit,
     so no third-party dependency or local reproving is needed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Postprocessing.PostprocessingResolutionMonotonicity

open D5.S3.ConceptDynamics.Postprocessing.PostprocessingKernelMonotonicity

universe u v w

/-- Equal query profiles remain equal after every deterministic postprocessing.
Thus ordinary function postprocessing can only enlarge the identification
kernel and cannot improve resolution. The deterministic carrier is faithful to
the source's function composition `g ∘ E_Q`; no measurability or finiteness
hypothesis is needed. -/
theorem postprocessing_cannot_improve_identification_resolution
    {Model : Type u} {Profile : Type v} {Output : Type w}
    (queryProfile : Model -> Profile) (postprocess : Profile -> Output) :
    Setoid.ker queryProfile ≤ Setoid.ker (postprocess ∘ queryProfile) :=
  postprocessing_kernel_mono queryProfile postprocess

#print axioms postprocessing_cannot_improve_identification_resolution

end D5.S3.ConceptDynamics.Postprocessing.PostprocessingResolutionMonotonicity
