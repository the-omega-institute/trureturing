/- GID: D5/S3/ConceptDynamics/InformationEscape/SharedInformationRoot
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/SharedInformationRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seal the complete registration closure including both unified causal transitions. -/

import D5.S3.ConceptDynamics.InformationEscape.InformationRoot
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot

open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open D5.S3.ConceptDynamics.ExperimentDesign.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.Gluing.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscape.SystemUnit

attribute [local instance]
  contextDecidableEq
  modelDecidableEq

local instance systemArenaStateDecidableEq : DecidableEq arena.toArena.State :=
  arena.toArena.stateDecidableEq

/-! The designated root consumes the fixed snapshot's complete registration
closure. Imported occurrences are sealed together without registering them again;
the frozen root retains its separate eleven-occurrence baseline. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
-- The seal decides twelve finite catalogs and kernel-checks every generated proof.
#seal_information_theory

end D5.S3.ConceptDynamics.InformationEscape.SharedInformationRoot
