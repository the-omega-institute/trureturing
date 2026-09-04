/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The FourState countermodel realizes its FLOW/FLOW/CUT law with a discrete kernel. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange

/- Library-search audit trail (2026-09-04): the source maps, readout, completion
   operations, and typed bundle compiler were exact repository hits and are reused.
   No pre-existing realization bridge or executable private-pair fact was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange

/-- Concrete FLOW/FLOW/CUT realization of the source countermodel. -/
def commutingCompletionRealization : PrimitiveRealization completionSignature where
  readout
    | .flowF => counterexampleF
    | .flowG => counterexampleG
    | .cut => counterexampleReadout
  anchor := fun i => Fin.elim0 i

/-- The legacy countermodel is equivalent to its object-bound realization law. -/
theorem commutativity_hypothesis_is_necessary_realization :
    LegacyPrimitiveRealization commutingCompletionArena CommutativityNecessaryStatement
      commutingCompletionRealization := by
  exact ⟨Iff.rfl⟩

/-- The complete FLOW/FLOW/CUT signature has four kernel classes. -/
theorem commutativity_hypothesis_is_necessary_partition_count :
    (Finset.univ.image (fun state : FourState =>
      (counterexampleF state, counterexampleG state,
        counterexampleReadout state))).card = 4 := by
  decide

/-- The private census pair `a,b` is separated by the compiled bundle. -/
theorem commutativity_hypothesis_is_necessary_private_pair :
    ¬ commutingCompletionRealization.toPrimitiveBundle.agrees FourState.a FourState.b := by
  intro h
  have hreadouts :=
    (PrimitiveRealization.toPrimitiveBundle_agrees_iff
      commutingCompletionRealization FourState.a FourState.b).1 h |>.1
  have hflowG := hreadouts CompletionReadout.flowG
  change FourState.b = FourState.c at hflowG
  exact FourState.noConfusion hflowG

example : commutingCompletionArena.toArena.Nondegenerate := by decide

end D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
