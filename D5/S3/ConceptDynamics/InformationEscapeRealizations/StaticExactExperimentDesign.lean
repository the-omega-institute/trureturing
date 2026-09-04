/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The frozen static exact-design theorem realizes its two CUT law with a three-class kernel. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign

/- Library-search audit trail (2026-09-04): exact searches found the frozen
   `static_exact_design`, canonical `jointReadout`, and typed realization compiler;
   they are reused directly. No existing legacy-realization bridge was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign

/-- Concrete change-X and change-Y response table. -/
def staticExactExperimentRealization : PrimitiveRealization staticSignature where
  readout := fun i model =>
    if i = (0 : StaticReadout) then decide (model = 1) else decide (model = 2)
  anchor := fun i => Fin.elim0 i

/-- The legacy theorem is equivalent to its object-bound realization law. -/
theorem static_exact_design_realization :
    LegacyPrimitiveRealization staticExactExperimentArena StaticExactDesignStatement
      staticExactExperimentRealization := by
  exact ⟨Iff.rfl⟩

/-- The complete CUT signature has the census-prescribed three kernel classes. -/
theorem static_exact_design_partition_count :
    (Finset.univ.image (fun model : Fin 3 =>
      (staticExactExperimentRealization.readout (0 : StaticReadout) model,
        staticExactExperimentRealization.readout (1 : StaticReadout) model))).card = 3 := by
  decide

/-- The private census pair `0,1` is separated by the compiled bundle. -/
theorem static_exact_design_private_pair :
    ¬ staticExactExperimentRealization.toPrimitiveBundle.agrees (0 : Fin 3) 1 := by decide

example : staticExactExperimentArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
