/- GID: D5/S3/ConceptDynamics/InformationEscapeCounting/Enumerations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeCounting/Enumerations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete arena enumerations execute the fused information-escape census. -/
import D5.S3.ConceptDynamics.InformationEscape.SystemUnit
import D5.S3.ConceptDynamics.InformationEscapeCounting.FusedCorrectness
import D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
import D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
import D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign

/- Library-search audit trail (2026-09-05):
   * Attempt 1 supplied all eleven explicit, complete state lists.
   * The realization modules supply the primitive bundles used by the censuses.
   * The two-index fixture follows the frozen Bool-pair coordinate catalogs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations

open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint

private def boolStates : List Bool := [false, true]

private def agendaStates : List Agenda :=
  (List.finRange 3).flatMap fun first =>
    (List.finRange 3).flatMap fun second =>
      (List.finRange 3).map fun final => ⟨first, second, final⟩

private def residueStates : List ResidueState :=
  [zeroState, tenState, fifteenState, twentyOneState]

private def spectrumStates : List SpectrumAtom :=
  [.t1, .t2, .t3, .t4, .t5]

private def contextStates : List BinaryInterpretationContext :=
  boolStates.flatMap fun admission =>
    boolStates.flatMap fun background =>
      boolStates.map fun goal =>
        { text := ()
          readerAdmission := admission
          background := background
          evaluationGoal := goal
          interpretationRule := () }

private abbrev InterventionModel :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM

private def interventionStates : List InterventionModel :=
  boolStates.flatMap fun ff =>
    boolStates.flatMap fun ft =>
      boolStates.flatMap fun tf =>
        boolStates.map fun tt =>
          ⟨fun exogenous treatment =>
            if exogenous then (if treatment then tt else tf)
            else if treatment then ft else ff⟩

private def unaryBoolTables : List (Bool -> Bool) :=
  [fun _ => false, fun bit => bit, fun bit => !bit, fun _ => true]

private abbrev ObservationModel :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM

private def observationStates : List ObservationModel :=
  [.xCausesY, .yCausesX].flatMap fun direction =>
    unaryBoolTables.flatMap fun root =>
      unaryBoolTables.map fun child => ⟨direction, root, child⟩

private def staticStates : List (Fin 3) := List.finRange 3

private def completionStates : List FourState := [.a, .b, .c, .d]

private def gluingStates : List (Bool × Bool × Bool) :=
  boolStates.flatMap fun first =>
    boolStates.flatMap fun second =>
      boolStates.map fun third => (first, second, third)

private def triggerOptions : List (Option Mechanism) :=
  [none, some .shooterA, some .shooterB]

private def preemptionStates : List PreemptionTrace :=
  triggerOptions.flatMap fun first =>
    triggerOptions.map fun second => fun time =>
      if time = 0 then first else second

end D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations

section

set_option linter.style.nameCheck false
set_option linter.style.haveILetI false

open D5.S3.ConceptDynamics.Aggregation.AgendaPower
open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.Coding.AdaptiveResidueIdentification
open D5.S3.ConceptDynamics.Completion.CommutingCompletionExchange
open D5.S3.ConceptDynamics.EscapeSpectrum.SpectrumCommitmentScope
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint

namespace D5.S3.ConceptDynamics.InformationEscapeArenas

namespace FirstThreeArenas.agendaPowerArena

/-- Deterministic enumeration companion for the agenda-power arena. -/
def __state_enumeration : Arena.StateEnumeration
    FirstThreeArenas.agendaPowerArena.toArena where
  states := agendaStates
  nodup := by change agendaStates.Nodup; decide
  complete := by
    letI := FirstThreeArenas.agendaFintype
    change agendaStates.toFinset = (Finset.univ : Finset Agenda); decide

end FirstThreeArenas.agendaPowerArena

namespace FirstThreeArenas.residueArena

/-- Deterministic enumeration companion for the adaptive-residue arena. -/
def __state_enumeration : Arena.StateEnumeration FirstThreeArenas.residueArena.toArena where
  states := residueStates
  nodup := by change residueStates.Nodup; decide
  complete := by change residueStates.toFinset = (Finset.univ : Finset ResidueState); decide

end FirstThreeArenas.residueArena

namespace FirstThreeArenas.spectrumArena

/-- Deterministic enumeration companion for the five-atom spectrum arena. -/
def __state_enumeration : Arena.StateEnumeration FirstThreeArenas.spectrumArena.toArena where
  states := spectrumStates
  nodup := by change spectrumStates.Nodup; decide
  complete := by change spectrumStates.toFinset = (Finset.univ : Finset SpectrumAtom); decide

end FirstThreeArenas.spectrumArena

namespace FourthFifthArenas.contextArena

/-- Deterministic enumeration companion for the interpretation-context arena. -/
def __state_enumeration : Arena.StateEnumeration FourthFifthArenas.contextArena.toArena where
  states := contextStates
  nodup := by
    letI := FourthFifthArenas.contextDecidableEq
    change contextStates.Nodup; decide
  complete := by
    letI := FourthFifthArenas.contextFintype
    letI := FourthFifthArenas.contextDecidableEq
    change contextStates.toFinset = (Finset.univ : Finset BinaryInterpretationContext); decide

end FourthFifthArenas.contextArena

namespace FourthFifthArenas.interventionArena

open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation

set_option maxHeartbeats 2000000 in
-- The explicit sixteen-table certificate needs the acceptance heartbeat cap.
/-- Deterministic enumeration companion for the counterfactual-intervention arena. -/
def __state_enumeration : Arena.StateEnumeration
    FourthFifthArenas.interventionArena.toArena where
  states := interventionStates
  nodup := by
    letI := FourthFifthArenas.modelDecidableEq
    change interventionStates.Nodup; decide
  complete := by
    letI := FourthFifthArenas.modelFintype
    letI := FourthFifthArenas.modelDecidableEq
    change interventionStates.toFinset = (Finset.univ : Finset DeterministicBoolSCM); decide

end FourthFifthArenas.interventionArena

namespace ObservationIntervention.observationInterventionArena

open D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation

/-- Deterministic enumeration companion for the observation-intervention arena. -/
def __state_enumeration : Arena.StateEnumeration
    ObservationIntervention.observationInterventionArena.toArena where
  states := observationStates
  nodup := by change observationStates.Nodup; decide
  complete := by
    change observationStates.toFinset = (Finset.univ : Finset DeterministicBoolSCM); decide

end ObservationIntervention.observationInterventionArena

namespace StaticExactExperimentDesign.staticExactExperimentArena

/-- Deterministic enumeration companion for the static exact-experiment arena. -/
def __state_enumeration : Arena.StateEnumeration
    StaticExactExperimentDesign.staticExactExperimentArena.toArena where
  states := staticStates
  nodup := List.nodup_finRange 3
  complete := by change staticStates.toFinset = (Finset.univ : Finset (Fin 3)); decide

end StaticExactExperimentDesign.staticExactExperimentArena

namespace CommutingCompletionExchange.commutingCompletionArena

/-- Deterministic enumeration companion for the commuting-completion arena. -/
def __state_enumeration : Arena.StateEnumeration
    CommutingCompletionExchange.commutingCompletionArena.toArena where
  states := completionStates
  nodup := by change completionStates.Nodup; decide
  complete := by change completionStates.toFinset = (Finset.univ : Finset FourState); decide

end CommutingCompletionExchange.commutingCompletionArena

namespace LocalLawGluingObstruction.localLawGluingArena

/-- Deterministic enumeration companion for the local-law-gluing arena. -/
def __state_enumeration : Arena.StateEnumeration
    LocalLawGluingObstruction.localLawGluingArena.toArena where
  states := gluingStates
  nodup := by change gluingStates.Nodup; decide
  complete := by
    change gluingStates.toFinset = (Finset.univ : Finset (Bool × Bool × Bool)); decide

end LocalLawGluingObstruction.localLawGluingArena

namespace EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena

/-- Deterministic enumeration companion for the preemption-trace arena. -/
def __state_enumeration : Arena.StateEnumeration
    EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena.toArena where
  states := preemptionStates
  nodup := by change preemptionStates.Nodup; decide
  complete := by change preemptionStates.toFinset = (Finset.univ : Finset PreemptionTrace); decide

end EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena

end D5.S3.ConceptDynamics.InformationEscapeArenas

namespace D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq

/-- Deterministic enumeration companion for the two-stage system arena. -/
def __state_enumeration : Arena.StateEnumeration SystemUnit.arena.toArena where
  states := [false, true]
  nodup := by decide
  complete := by decide

end D5.S3.ConceptDynamics.InformationEscape.SystemUnit.arena

end

namespace D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.Catalog
open D5.S3.ConceptDynamics.InformationEscapeArenas.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.FirstThreeArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
open D5.S3.ConceptDynamics.InformationEscapeArenas.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeArenas.StaticExactExperimentDesign
open D5.S3.ConceptDynamics.InformationEscapeRealizations.CommutingCompletionExchange
open D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FirstThreeRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
open D5.S3.ConceptDynamics.InformationEscapeRealizations.LocalLawGluingObstruction
open D5.S3.ConceptDynamics.InformationEscapeRealizations.ObservationIntervention
open D5.S3.ConceptDynamics.InformationEscapeRealizations.StaticExactExperimentDesign

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq

set_option linter.style.haveILetI false in
private def singletonCatalog {arena : PrimitiveLawArena.{u, v, w}}
    (realization : PrimitiveRealization arena.signature) :
    Catalog.{u, v, 0} arena.toArena := by
  letI := arena.toArena.stateDecidableEq
  exact
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      theoremAt := fun _ =>
        { primitives := realization.toPrimitiveBundle
          Statement := True
          proof := True.intro } }

private def singletonCounts {arena : PrimitiveLawArena.{u, v, w}}
    (realization : PrimitiveRealization arena.signature)
    (states : Arena.StateEnumeration arena.toArena) : FusedCounts (Fin 1) :=
  (singletonCatalog realization).fusedCounts states (finIndexEnumeration 1)

private abbrev boolPairArena : Arena := Arena.ofFintype (Bool × Bool)

private abbrev coordinateBundle (readout : Bool × Bool -> Bool) :
    PrimitiveBundle (Bool × Bool) where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel readout⟩

private abbrev coordinateUnit (readout : Bool × Bool -> Bool) :
    TheoremUnit boolPairArena where
  primitives := coordinateBundle readout
  Statement := True
  proof := trivial

private def twoTheoremCatalog : Catalog boolPairArena where
  Index := Fin 2
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := fun index =>
    if index = 0 then coordinateUnit Prod.fst else coordinateUnit Prod.snd

private def boolPairEnumeration : Arena.StateEnumeration boolPairArena where
  states := [(false, false), (false, true), (true, false), (true, true)]
  nodup := by decide
  complete := by decide

private def twoTheoremCounts : FusedCounts (Fin 2) :=
  twoTheoremCatalog.fusedCounts boolPairEnumeration (finIndexEnumeration 2)

set_option linter.style.setOption false in
-- The executable censuses share the acceptance resource envelope.
section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

example : (singletonCounts agendaPowerRealization
    agendaPowerArena.__state_enumeration).unique 0 = 570 := by decide
example : (singletonCounts residueRealization
    residueArena.__state_enumeration).unique 0 = 12 := by decide
example : (singletonCounts spectrumRealization
    spectrumArena.__state_enumeration).unique 0 = 20 := by decide
example : (singletonCounts contextRealization
    contextArena.__state_enumeration).unique 0 = 56 := by decide
example : (singletonCounts interventionRealization
    interventionArena.__state_enumeration).unique 0 = 240 := by decide
example : (singletonCounts observationInterventionRealization
    observationInterventionArena.__state_enumeration).unique 0 = 968 := by decide
example : (singletonCounts staticExactExperimentRealization
    staticExactExperimentArena.__state_enumeration).unique 0 = 6 := by decide
example : (singletonCounts commutingCompletionRealization
    commutingCompletionArena.__state_enumeration).unique 0 = 12 := by decide
example : (singletonCounts localLawGluingRealization
    localLawGluingArena.__state_enumeration).unique 0 = 48 := by decide
example : (singletonCounts endStateOmitsPreemptingCauseRealization
    endStateOmitsPreemptingCauseArena.__state_enumeration).unique 0 = 60 := by decide
example : (singletonCounts SystemUnit.systemRealization
    SystemUnit.arena.__state_enumeration).unique 0 = 2 := by decide

example : twoTheoremCounts.full = 0 ∧
    twoTheoremCounts.unique 0 = 4 ∧ twoTheoremCounts.unique 1 = 4 := by decide

example : 0 < (singletonCounts agendaPowerRealization
    agendaPowerArena.__state_enumeration).unique 0 := by decide
example : 0 < (singletonCounts observationInterventionRealization
    observationInterventionArena.__state_enumeration).unique 0 := by decide
example : ∀ index, 0 < twoTheoremCounts.unique index := by decide

end

end D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
