/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalCatalog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unified causal catalogs certify irredundancy and layered counts. -/

import D5.S3.ConceptDynamics.InformationEscape.Laws
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment

 /- Library-search audit trail (2026-09-05):
   * Exact repository hits `TheoremUnit`, `Catalog`, `CatalogIrredundant`,
     `offDiagonalPairs`, and the escape/unique-capture APIs are imported and reused.
   * `Catalog.uniqueCaptureCount_pos_iff_witness` turns the two named branch-local
     causal witnesses directly into irredundancy, without importing census code.
   * Searches for unified cumulative catalogs, causal layered Finsets, and the
     CAUSAL-IE-003 owner found only specification section 43.1, not landed code.
   * Pinned Mathlib supplies list maps/appends, finite coproduct instances, and
     decidable finite-function equality used by the reflected certificates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog
open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas
open D5.S3.ConceptDynamics.Interventions
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq
local instance : Fintype IC.Model :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelFintype
local instance : DecidableEq IC.Model :=
  D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq
local instance : DecidableEq OI.Model :=
  ObservationIntervention.instDecidableEqDeterministicBoolSCM
local instance : Fintype UnifiedBoolSCM := inferInstance
local instance : DecidableEq UnifiedBoolSCM := inferInstance
local instance : DecidableEq ICCFTable := inferInstance
local instance : DecidableEq CfOut := inferInstance
private def cumulativeReadoutBundle {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) : PrimitiveBundle UnifiedBoolSCM where
  Index := Fin 1
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  atom := fun _ => ⟨.cut, cutKernel readout⟩
private theorem cumulativeReadoutBundle_agrees_iff
    {Output : Type} [DecidableEq Output] (readout : UnifiedBoolSCM → Output)
    (left right : UnifiedBoolSCM) :
    (cumulativeReadoutBundle readout).agrees left right ↔
      readout left = readout right := by
  constructor
  · intro agreement
    simpa [cumulativeReadoutBundle] using agreement (0 : Fin 1)
  · intro equality _index
    simpa [cumulativeReadoutBundle] using equality
private def cumulativeReadoutUnit {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) : TheoremUnit.{0, 0} unifiedArena where
  primitives := cumulativeReadoutBundle readout
  Statement := True
  proof := True.intro
-- The analysis-view observation unit carries exactly the `ObsU` kernel.
def unifiedObservationUnit : TheoremUnit.{0, 0} unifiedArena :=
  cumulativeReadoutUnit ObsU
-- The analysis-view intervention unit carries exactly the `IntU` kernel.
def unifiedInterventionUnit : TheoremUnit.{0, 0} unifiedArena :=
  cumulativeReadoutUnit IntU
-- The analysis-view counterfactual unit carries exactly the `CfU` kernel.
def unifiedCounterfactualUnit : TheoremUnit.{0, 0} unifiedArena :=
  cumulativeReadoutUnit CfU
inductive UnifiedCumulativeReadoutIndex
  | observation
  | intervention
  | counterfactual
  deriving DecidableEq
instance : Fintype UnifiedCumulativeReadoutIndex where
  elems := {.observation, .intervention, .counterfactual}
  complete := by intro index; cases index <;> simp
-- The flat three-member cumulative analysis-view catalog.
def unifiedCumulativeCatalog : Catalog.{0, 0, 0} unifiedArena where
  Index := UnifiedCumulativeReadoutIndex
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt
    | .observation => unifiedObservationUnit
    | .intervention => unifiedInterventionUnit
    | .counterfactual => unifiedCounterfactualUnit
-- The frozen OI occurrence transported faithfully to the unified arena.
def unifiedObservationInterventionUnit : TheoremUnit.{0, 0} unifiedArena :=
  LegacyPrimitiveRealization.toTheoremUnit
    observation_intervention_unified_realization
    ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
-- The frozen IC occurrence transported faithfully to the unified arena.
def unifiedInterventionCounterfactualUnit : TheoremUnit.{0, 0} unifiedArena :=
  LegacyPrimitiveRealization.toTheoremUnit
    intervention_counterfactual_unified_realization
    InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
inductive UnifiedFrozenTransitionIndex
  | observationIntervention
  | interventionCounterfactual
  deriving DecidableEq

instance : Fintype UnifiedFrozenTransitionIndex where
  elems := {.observationIntervention, .interventionCounterfactual}
  complete := by intro index; cases index <;> simp

-- The two faithful frozen theorem occurrences on the unified arena.
def unifiedFrozenTransitionCatalog : Catalog.{0, 0, 0} unifiedArena where
  Index := UnifiedFrozenTransitionIndex
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt
    | .observationIntervention => unifiedObservationInterventionUnit
    | .interventionCounterfactual => unifiedInterventionCounterfactualUnit

-- Each named strictness witness is invisible to the theorem on the opposite branch.
-- CAUSAL-IE-003.
theorem unified_frozen_transition_catalog_irredundant :
    CatalogIrredundant unifiedFrozenTransitionCatalog := by
  rw [catalogIrredundant_iff_forall_pos]
  intro index
  rw [unifiedFrozenTransitionCatalog.uniqueCaptureCount_pos_iff_witness]
  cases index with
  | observationIntervention =>
      rcases ObservationInterventionSeparation.observation_strictly_weaker_than_intervention
        with ⟨left, right, equalObservation, unequalIntervention⟩
      refine ⟨.inr left, .inr right, ?_, ?_, ?_⟩
      · intro equalModel
        exact unequalIntervention (congrArg OI.Int (Sum.inr.inj equalModel))
      · intro candidate candidateNe
        cases candidate with
        | observationIntervention => exact False.elim (candidateNe rfl)
        | interventionCounterfactual =>
            apply (PrimitiveRealization.toPrimitiveBundle_agrees_iff
              interventionCounterfactualUnifiedRealization _ _).2
            constructor
            · intro readout
              cases readout <;> rfl
            · intro anchor
              exact Fin.elim0 anchor
      · intro agreement
        have readouts := (PrimitiveRealization.toPrimitiveBundle_agrees_iff
          observationInterventionUnifiedRealization _ _).1 agreement |>.1
        exact unequalIntervention (Option.some.inj (readouts .intervention))
  | interventionCounterfactual =>
      rcases InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual
        with ⟨left, right, equalIntervention, unequalCounterfactual⟩
      refine ⟨.inl left, .inl right, ?_, ?_, ?_⟩
      · intro equalModel
        exact unequalCounterfactual (congrArg IC.CF (Sum.inl.inj equalModel))
      · intro candidate candidateNe
        cases candidate with
        | observationIntervention =>
            apply (PrimitiveRealization.toPrimitiveBundle_agrees_iff
              observationInterventionUnifiedRealization _ _).2
            constructor
            · intro readout
              cases readout <;> rfl
            · intro anchor
              exact Fin.elim0 anchor
        | interventionCounterfactual => exact False.elim (candidateNe rfl)
      · intro agreement
        have readouts := (PrimitiveRealization.toPrimitiveBundle_agrees_iff
          interventionCounterfactualUnifiedRealization _ _).1 agreement |>.1
        exact unequalCounterfactual (Option.some.inj (readouts .counterfactual))

-- All ordered off-diagonal pairs in the unified causal arena.
def unifiedOffDiagonalPairs : Finset (UnifiedBoolSCM × UnifiedBoolSCM) := by
  letI := unifiedArena.stateFintype
  letI := unifiedArena.stateDecidableEq
  exact offDiagonalPairs UnifiedBoolSCM

private theorem mem_unifiedOffDiagonalPairs_iff
    (pair : UnifiedBoolSCM × UnifiedBoolSCM) :
    pair ∈ unifiedOffDiagonalPairs ↔ pair.1 ≠ pair.2 := by
  simp [unifiedOffDiagonalPairs, offDiagonalPairs]

private theorem mem_arenaOffDiagonalPairs_iff
    (pair : unifiedArena.State × unifiedArena.State) :
    pair ∈ offDiagonalPairs unifiedArena.State ↔ pair.1 ≠ pair.2 := by
  simp [offDiagonalPairs]

private def cumulativeEscapePairs {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) : Finset (UnifiedBoolSCM × UnifiedBoolSCM) :=
  unifiedOffDiagonalPairs.filter fun pair => readout pair.1 = readout pair.2

-- Ordered off-diagonal pairs escaping cumulative observation.
def E_obs : Finset (UnifiedBoolSCM × UnifiedBoolSCM) := cumulativeEscapePairs ObsU

-- Ordered off-diagonal pairs escaping cumulative intervention.
def E_int : Finset (UnifiedBoolSCM × UnifiedBoolSCM) := cumulativeEscapePairs IntU

-- Ordered off-diagonal pairs escaping cumulative counterfactual information.
def E_cf : Finset (UnifiedBoolSCM × UnifiedBoolSCM) := cumulativeEscapePairs CfU

-- Pairs captured already by cumulative observation.
def L_obs : Finset (UnifiedBoolSCM × UnifiedBoolSCM) :=
  unifiedOffDiagonalPairs.filter fun pair => ObsU pair.1 ≠ ObsU pair.2

-- Pairs first captured by cumulative intervention.
def L_int : Finset (UnifiedBoolSCM × UnifiedBoolSCM) :=
  unifiedOffDiagonalPairs.filter fun pair =>
    ObsU pair.1 = ObsU pair.2 ∧ IntU pair.1 ≠ IntU pair.2

-- Pairs first captured by cumulative counterfactual information.
def L_cf : Finset (UnifiedBoolSCM × UnifiedBoolSCM) :=
  unifiedOffDiagonalPairs.filter fun pair =>
    IntU pair.1 = IntU pair.2 ∧ CfU pair.1 ≠ CfU pair.2

-- All off-diagonal pairs outside the finest cumulative kernel.
def capturedByCounterfactual : Finset (UnifiedBoolSCM × UnifiedBoolSCM) :=
  unifiedOffDiagonalPairs.filter fun pair => CfU pair.1 ≠ CfU pair.2

-- The three ordered cumulative increments are pairwise disjoint.
theorem unified_layered_increments_pairwise_disjoint :
    Disjoint L_obs L_int ∧ Disjoint L_obs L_cf ∧ Disjoint L_int L_cf := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro pair pairObs pairInt
    exact (Finset.mem_filter.mp pairObs).2 (Finset.mem_filter.mp pairInt).2.1
  · constructor
    · apply Finset.disjoint_left.mpr
      intro pair pairObs pairCf
      have equalInt := (Finset.mem_filter.mp pairCf).2.1
      have equalObs :=
        unified_observation_intervention_strict_refinement.1 pair.1 pair.2 equalInt
      exact (Finset.mem_filter.mp pairObs).2 equalObs
    · apply Finset.disjoint_left.mpr
      intro pair pairInt pairCf
      exact (Finset.mem_filter.mp pairInt).2.2 (Finset.mem_filter.mp pairCf).2.1

-- The three ordered increments partition `D_A \ K_cf`.
theorem unified_layered_increments_partition :
    (L_obs ∪ L_int) ∪ L_cf = capturedByCounterfactual := by
  apply Finset.ext
  intro pair
  simp only [Finset.mem_union, L_obs, L_int, L_cf, capturedByCounterfactual,
    Finset.mem_filter]
  constructor
  · intro membership
    rcases membership with (pairObs | pairInt) | pairCf
    · rcases pairObs with ⟨offDiagonal, unequalObs⟩
      refine ⟨offDiagonal, ?_⟩
      intro equalCf
      have equalInt :=
        unified_intervention_counterfactual_strict_refinement.1 pair.1 pair.2 equalCf
      exact unequalObs
        (unified_observation_intervention_strict_refinement.1 pair.1 pair.2 equalInt)
    · rcases pairInt with ⟨offDiagonal, equalObs, unequalInt⟩
      refine ⟨offDiagonal, ?_⟩
      intro equalCf
      exact unequalInt
        (unified_intervention_counterfactual_strict_refinement.1 pair.1 pair.2 equalCf)
    · rcases pairCf with ⟨offDiagonal, equalInt, unequalCf⟩
      exact ⟨offDiagonal, unequalCf⟩
  · rintro ⟨offDiagonal, unequalCf⟩
    by_cases equalObs : ObsU pair.1 = ObsU pair.2
    · by_cases equalInt : IntU pair.1 = IntU pair.2
      · exact Or.inr ⟨offDiagonal, equalInt, unequalCf⟩
      · exact Or.inl (Or.inr ⟨offDiagonal, equalObs, equalInt⟩)
    · exact Or.inl (Or.inl ⟨offDiagonal, equalObs⟩)

end D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog
