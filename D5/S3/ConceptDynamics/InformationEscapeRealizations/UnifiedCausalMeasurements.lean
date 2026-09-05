/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalMeasurements
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalMeasurements
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact reflected measurements certify the unified causal census. -/

import D5.S3.ConceptDynamics.InformationEscapeCounting.Enumerations
import D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

/-! The reflected census is isolated from the public causal catalog API. In particular,
the two private zero-count results below are only the section 43.1 causal fixed-catalog
instance of CIRPT-IE-024. They do not claim the general law owned by AnalysisLaws. -/

/- Library-search audit trail (2026-09-05):
   * Exact repository hits `Arena.StateEnumeration`, `Catalog.fusedCounts`, and the
     fused full/unique correctness theorems are reused through `Enumerations`.
   * The landed 16-state IC and 32-state OI enumerations are composed rather than
     duplicated, while the public catalog and layer definitions are imported intact.
   * Pinned Mathlib supplies finite coproduct computation and kernel `decide`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalMeasurements

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas
open D5.S3.ConceptDynamics.Interventions
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
open D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalCatalog

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

private abbrev interventionEnumeration :=
  FourthFifthArenas.interventionArena.__state_enumeration
private abbrev observationEnumeration :=
  ObservationIntervention.observationInterventionArena.__state_enumeration
private def unifiedStates : List UnifiedBoolSCM :=
  interventionEnumeration.states.map Sum.inl ++
    observationEnumeration.states.map Sum.inr

private def unifiedStateEnumeration : Arena.StateEnumeration unifiedArena where
  states := unifiedStates
  nodup := by
    apply List.Nodup.append
    · exact interventionEnumeration.nodup.map Sum.inl_injective
    · exact observationEnumeration.nodup.map Sum.inr_injective
    · apply List.disjoint_left.2
      intro state stateInLeft stateInRight
      rcases List.mem_map.1 stateInLeft with ⟨model, _, rfl⟩
      rcases List.mem_map.1 stateInRight with ⟨model, _, impossible⟩
      exact Sum.inr_ne_inl impossible
  complete := by
    apply Finset.eq_univ_of_forall
    intro state
    cases state with
    | inl model =>
        have modelMem : model ∈ interventionEnumeration.states := by
          have : model ∈ interventionEnumeration.states.toFinset := by
            rw [interventionEnumeration.complete]
            exact Finset.mem_univ model
          exact List.mem_toFinset.mp this
        apply List.mem_toFinset.mpr
        unfold unifiedStates
        exact List.mem_append.mpr (Or.inl
          (List.mem_map.mpr ⟨model, modelMem, rfl⟩))
    | inr model =>
        have modelMem : model ∈ observationEnumeration.states := by
          have : model ∈ observationEnumeration.states.toFinset := by
            rw [observationEnumeration.complete]
            exact Finset.mem_univ model
          exact List.mem_toFinset.mp this
        apply List.mem_toFinset.mpr
        unfold unifiedStates
        exact List.mem_append.mpr (Or.inr
          (List.mem_map.mpr ⟨model, modelMem, rfl⟩))

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

private def unifiedCumulativeIndexEnumeration :
    @Catalog.IndexEnumeration unifiedCumulativeCatalog.Index
      unifiedCumulativeCatalog.indexDecidableEq := by
  change @Catalog.IndexEnumeration UnifiedCumulativeReadoutIndex _
  exact
    { indices := [.observation, .intervention, .counterfactual]
      nodup := by decide
      complete := by intro index; cases index <;> simp }

private def emptyCumulativeCatalog : Catalog.{0, 0, 0} unifiedArena :=
  Catalog.ofVector fun index : Fin 0 => Fin.elim0 index

private def singletonCumulativeCatalog (unit : TheoremUnit.{0, 0} unifiedArena) :
    Catalog.{0, 0, 0} unifiedArena :=
  Catalog.ofVector fun _ : Fin 1 => unit

private def emptyCumulativeIndexEnumeration :
    @Catalog.IndexEnumeration emptyCumulativeCatalog.Index
      emptyCumulativeCatalog.indexDecidableEq := by
  change @Catalog.IndexEnumeration (Fin 0) _
  exact
    { indices := []
      nodup := List.nodup_nil
      complete := by intro index; exact Fin.elim0 index }

private def singletonCumulativeIndexEnumeration
    (unit : TheoremUnit.{0, 0} unifiedArena) :
    @Catalog.IndexEnumeration (singletonCumulativeCatalog unit).Index
      (singletonCumulativeCatalog unit).indexDecidableEq := by
  change @Catalog.IndexEnumeration (Fin 1) _
  exact
    { indices := [0]
      nodup := by simp
      complete := by intro index; fin_cases index; simp }

private theorem emptyCumulativeCatalog_escapePairs_full :
    emptyCumulativeCatalog.escapePairs emptyCumulativeCatalog.fullIndexSet =
      unifiedOffDiagonalPairs := by
  ext pair
  constructor
  · intro membership
    have offDiagonal := (Finset.mem_filter.mp membership).1
    exact (mem_unifiedOffDiagonalPairs_iff pair).2
      ((mem_arenaOffDiagonalPairs_iff pair).1 offDiagonal)
  · intro offDiagonal
    apply Finset.mem_filter.mpr
    refine ⟨(mem_arenaOffDiagonalPairs_iff pair).2
      ((mem_unifiedOffDiagonalPairs_iff pair).1 offDiagonal), ?_⟩
    apply (emptyCumulativeCatalog.indistinguishable_iff_forall
      emptyCumulativeCatalog.fullIndexSet pair.1 pair.2).2
    intro index
    exact Fin.elim0 index

private theorem singletonCumulativeCatalog_escapePairs_full
    {Output : Type} [DecidableEq Output] (readout : UnifiedBoolSCM → Output) :
    (singletonCumulativeCatalog (cumulativeReadoutUnit readout)).escapePairs
        (singletonCumulativeCatalog
          (cumulativeReadoutUnit readout)).fullIndexSet =
      cumulativeEscapePairs readout := by
  ext pair
  constructor
  · intro membership
    rcases Finset.mem_filter.mp membership with ⟨offDiagonal, agreement⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_unifiedOffDiagonalPairs_iff pair).2
      ((mem_arenaOffDiagonalPairs_iff pair).1 offDiagonal), ?_⟩
    have atIndex :=
      ((singletonCumulativeCatalog
        (cumulativeReadoutUnit readout)).indistinguishable_iff_forall
          (singletonCumulativeCatalog
            (cumulativeReadoutUnit readout)).fullIndexSet pair.1 pair.2).1
        agreement (0 : Fin 1) (Finset.mem_univ _)
    exact (cumulativeReadoutBundle_agrees_iff readout pair.1 pair.2).1 atIndex
  · intro membership
    rcases Finset.mem_filter.mp membership with ⟨offDiagonal, equalReadout⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_arenaOffDiagonalPairs_iff pair).2
      ((mem_unifiedOffDiagonalPairs_iff pair).1 offDiagonal), ?_⟩
    apply ((singletonCumulativeCatalog
      (cumulativeReadoutUnit readout)).indistinguishable_iff_forall
        (singletonCumulativeCatalog
          (cumulativeReadoutUnit readout)).fullIndexSet pair.1 pair.2).2
    intro _index _
    exact (cumulativeReadoutBundle_agrees_iff readout pair.1 pair.2).2 equalReadout

private def emptyCumulativeCounts : Catalog.FusedCounts (Fin 0) :=
  emptyCumulativeCatalog.fusedCounts unifiedStateEnumeration
    emptyCumulativeIndexEnumeration
private def observationCumulativeCounts : Catalog.FusedCounts (Fin 1) :=
  (singletonCumulativeCatalog unifiedObservationUnit).fusedCounts unifiedStateEnumeration
    (singletonCumulativeIndexEnumeration unifiedObservationUnit)
private def interventionCumulativeCounts : Catalog.FusedCounts (Fin 1) :=
  (singletonCumulativeCatalog unifiedInterventionUnit).fusedCounts unifiedStateEnumeration
    (singletonCumulativeIndexEnumeration unifiedInterventionUnit)
private def counterfactualCumulativeCounts : Catalog.FusedCounts (Fin 1) :=
  (singletonCumulativeCatalog unifiedCounterfactualUnit).fusedCounts unifiedStateEnumeration
    (singletonCumulativeIndexEnumeration unifiedCounterfactualUnit)
private def flatCumulativeCounts : Catalog.FusedCounts UnifiedCumulativeReadoutIndex :=
  unifiedCumulativeCatalog.fusedCounts unifiedStateEnumeration
    unifiedCumulativeIndexEnumeration

private def icOffDiagonalPairs : Finset (IC.Model × IC.Model) :=
  offDiagonalPairs IC.Model
private def oiOffDiagonalPairs : Finset (OI.Model × OI.Model) :=
  offDiagonalPairs OI.Model
private def icEscapePairs {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) : Finset (IC.Model × IC.Model) :=
  icOffDiagonalPairs.filter fun pair =>
    readout (.inl pair.1) = readout (.inl pair.2)
private def oiEscapePairs {Output : Type} [DecidableEq Output]
    (readout : UnifiedBoolSCM → Output) : Finset (OI.Model × OI.Model) :=
  oiOffDiagonalPairs.filter fun pair =>
    readout (.inr pair.1) = readout (.inr pair.2)

private def icPairEmbedding : (IC.Model × IC.Model) ↪
    (UnifiedBoolSCM × UnifiedBoolSCM) where
  toFun := fun pair => (.inl pair.1, .inl pair.2)
  inj' := by
    intro left right equality
    exact Prod.ext (Sum.inl.inj (congrArg Prod.fst equality))
      (Sum.inl.inj (congrArg Prod.snd equality))
private def oiPairEmbedding : (OI.Model × OI.Model) ↪
    (UnifiedBoolSCM × UnifiedBoolSCM) where
  toFun := fun pair => (.inr pair.1, .inr pair.2)
  inj' := by
    intro left right equality
    exact Prod.ext (Sum.inr.inj (congrArg Prod.fst equality))
      (Sum.inr.inj (congrArg Prod.snd equality))

private theorem mem_ic_pair_map_iff
    (pairs : Finset (IC.Model × IC.Model)) (pair : UnifiedBoolSCM × UnifiedBoolSCM) :
    pair ∈ pairs.map icPairEmbedding ↔
      ∃ left right, pair = (.inl left, .inl right) ∧ (left, right) ∈ pairs := by
  constructor
  · intro membership
    rcases Finset.mem_map.mp membership with ⟨source, sourceMem, equality⟩
    exact ⟨source.1, source.2, equality.symm, sourceMem⟩
  · rintro ⟨left, right, rfl, membership⟩
    exact Finset.mem_map.mpr ⟨(left, right), membership, rfl⟩
private theorem mem_oi_pair_map_iff
    (pairs : Finset (OI.Model × OI.Model)) (pair : UnifiedBoolSCM × UnifiedBoolSCM) :
    pair ∈ pairs.map oiPairEmbedding ↔
      ∃ left right, pair = (.inr left, .inr right) ∧ (left, right) ∈ pairs := by
  constructor
  · intro membership
    rcases Finset.mem_map.mp membership with ⟨source, sourceMem, equality⟩
    exact ⟨source.1, source.2, equality.symm, sourceMem⟩
  · rintro ⟨left, right, rfl, membership⟩
    exact Finset.mem_map.mpr ⟨(left, right), membership, rfl⟩

set_option maxHeartbeats 8000000 in
-- Branch-local reflection avoids a much larger coproduct reduction.
private theorem ic_escape_card_measurements :
    (icEscapePairs ObsU).card = 80 ∧
      (icEscapePairs IntU).card = 20 ∧
      (icEscapePairs CfU).card = 0 := by
  simp only [icEscapePairs, ObsU, IntU, CfU, Sum.inl.injEq]
  decide

set_option maxHeartbeats 8000000 in
-- Branch-local reflection avoids a much larger coproduct reduction.
private theorem oi_escape_card_measurements :
    (oiEscapePairs ObsU).card = 56 ∧
      (oiEscapePairs IntU).card = 24 ∧
      (oiEscapePairs CfU).card = 0 := by
  simp only [oiEscapePairs, ObsU, IntU, CfU, Sum.inr.injEq]
  decide

private theorem branch_pair_images_disjoint
    (icPairs : Finset (IC.Model × IC.Model))
    (oiPairs : Finset (OI.Model × OI.Model)) :
    Disjoint (icPairs.map icPairEmbedding) (oiPairs.map oiPairEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro pair pairInIC pairInOI
  rcases Finset.mem_map.mp pairInIC with ⟨icPair, _, icEquality⟩
  rcases Finset.mem_map.mp pairInOI with ⟨oiPair, _, oiEquality⟩
  have impossible : (Sum.inl icPair.1 : UnifiedBoolSCM) = Sum.inr oiPair.1 :=
    (congrArg Prod.fst icEquality).trans (congrArg Prod.fst oiEquality).symm
  exact Sum.inl_ne_inr impossible

private theorem E_obs_eq_branch_union :
    E_obs =
      (icEscapePairs ObsU).map icPairEmbedding ∪
        (oiEscapePairs ObsU).map oiPairEmbedding := by
  change cumulativeEscapePairs ObsU = _
  ext pair
  rw [Finset.mem_union, mem_ic_pair_map_iff, mem_oi_pair_map_iff]
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;>
    simp [cumulativeEscapePairs, unifiedOffDiagonalPairs,
      icEscapePairs, oiEscapePairs, icOffDiagonalPairs, oiOffDiagonalPairs,
      offDiagonalPairs, ObsU]
private theorem E_int_eq_branch_union :
    E_int =
      (icEscapePairs IntU).map icPairEmbedding ∪
        (oiEscapePairs IntU).map oiPairEmbedding := by
  change cumulativeEscapePairs IntU = _
  ext pair
  rw [Finset.mem_union, mem_ic_pair_map_iff, mem_oi_pair_map_iff]
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;>
    simp [cumulativeEscapePairs, unifiedOffDiagonalPairs,
      icEscapePairs, oiEscapePairs, icOffDiagonalPairs, oiOffDiagonalPairs,
      offDiagonalPairs, IntU]
private theorem E_cf_eq_branch_union :
    E_cf =
      (icEscapePairs CfU).map icPairEmbedding ∪
        (oiEscapePairs CfU).map oiPairEmbedding := by
  change cumulativeEscapePairs CfU = _
  ext pair
  rw [Finset.mem_union, mem_ic_pair_map_iff, mem_oi_pair_map_iff]
  rcases pair with ⟨left, right⟩
  cases left <;> cases right <;>
    simp [cumulativeEscapePairs, unifiedOffDiagonalPairs,
      icEscapePairs, oiEscapePairs, icOffDiagonalPairs, oiOffDiagonalPairs,
      offDiagonalPairs, CfU]

private theorem E_obs_card : E_obs.card = 136 := by
  rw [E_obs_eq_branch_union,
    Finset.card_union_of_disjoint (branch_pair_images_disjoint _ _),
    Finset.card_map, Finset.card_map, ic_escape_card_measurements.1,
    oi_escape_card_measurements.1]

private theorem E_int_card : E_int.card = 44 := by
  rw [E_int_eq_branch_union,
    Finset.card_union_of_disjoint (branch_pair_images_disjoint _ _),
    Finset.card_map, Finset.card_map, ic_escape_card_measurements.2.1,
    oi_escape_card_measurements.2.1]

private theorem E_cf_card : E_cf.card = 0 := by
  rw [E_cf_eq_branch_union,
    Finset.card_union_of_disjoint (branch_pair_images_disjoint _ _),
    Finset.card_map, Finset.card_map, ic_escape_card_measurements.2.2,
    oi_escape_card_measurements.2.2]

private theorem unifiedOffDiagonalPairs_card : unifiedOffDiagonalPairs.card = 2256 := by
  calc
    unifiedOffDiagonalPairs.card = escapeDenominator unifiedArena := rfl
    _ = unifiedArena.card * (unifiedArena.card - 1) := escapeDenominator_eq unifiedArena
    _ = 2256 := by decide

private theorem E_obs_subset_offDiagonal : E_obs ⊆ unifiedOffDiagonalPairs := by
  intro pair membership
  exact (Finset.mem_filter.mp membership).1

private theorem E_int_subset_E_obs : E_int ⊆ E_obs := by
  intro pair membership
  rcases Finset.mem_filter.mp membership with ⟨offDiagonal, equalInt⟩
  apply Finset.mem_filter.mpr
  exact ⟨offDiagonal,
    unified_observation_intervention_strict_refinement.1 pair.1 pair.2 equalInt⟩

private theorem E_cf_subset_E_int : E_cf ⊆ E_int := by
  intro pair membership
  rcases Finset.mem_filter.mp membership with ⟨offDiagonal, equalCf⟩
  apply Finset.mem_filter.mpr
  exact ⟨offDiagonal,
    unified_intervention_counterfactual_strict_refinement.1 pair.1 pair.2 equalCf⟩

private theorem L_obs_eq_sdiff : L_obs = unifiedOffDiagonalPairs \ E_obs := by
  change L_obs = unifiedOffDiagonalPairs \ cumulativeEscapePairs ObsU
  ext pair
  simp only [Finset.mem_sdiff, L_obs, cumulativeEscapePairs,
    Finset.mem_filter]
  tauto

private theorem L_int_eq_sdiff : L_int = E_obs \ E_int := by
  change L_int = cumulativeEscapePairs ObsU \ cumulativeEscapePairs IntU
  ext pair
  simp only [Finset.mem_sdiff, L_int, cumulativeEscapePairs,
    Finset.mem_filter]
  tauto

private theorem L_cf_eq_sdiff : L_cf = E_int \ E_cf := by
  change L_cf = cumulativeEscapePairs IntU \ cumulativeEscapePairs CfU
  ext pair
  simp only [Finset.mem_sdiff, L_cf, cumulativeEscapePairs,
    Finset.mem_filter]
  tauto

private theorem cumulative_edge_card_measurements :
    L_obs.card = 2120 ∧ L_int.card = 92 ∧ L_cf.card = 44 := by
  constructor
  · rw [L_obs_eq_sdiff, Finset.card_sdiff_of_subset E_obs_subset_offDiagonal,
      unifiedOffDiagonalPairs_card, E_obs_card]
  · constructor
    · rw [L_int_eq_sdiff, Finset.card_sdiff_of_subset E_int_subset_E_obs,
        E_obs_card, E_int_card]
    · rw [L_cf_eq_sdiff, Finset.card_sdiff_of_subset E_cf_subset_E_int,
        E_int_card, E_cf_card]

private theorem empty_fused_full_eq_offDiagonal :
    emptyCumulativeCounts.full = unifiedOffDiagonalPairs.card := by
  unfold emptyCumulativeCounts
  exact (emptyCumulativeCatalog.fusedFull_eq_escapeNumerator
    unifiedStateEnumeration emptyCumulativeIndexEnumeration).trans
      (congrArg Finset.card emptyCumulativeCatalog_escapePairs_full)

private theorem singleton_fused_full_eq_escape_card
    {Output : Type} [DecidableEq Output] (readout : UnifiedBoolSCM → Output) :
    ((singletonCumulativeCatalog (cumulativeReadoutUnit readout)).fusedCounts
      unifiedStateEnumeration
      (singletonCumulativeIndexEnumeration
        (cumulativeReadoutUnit readout))).full =
      (cumulativeEscapePairs readout).card := by
  exact ((singletonCumulativeCatalog
    (cumulativeReadoutUnit readout)).fusedFull_eq_escapeNumerator
      unifiedStateEnumeration
      (singletonCumulativeIndexEnumeration (cumulativeReadoutUnit readout))).trans
        (congrArg Finset.card
          (singletonCumulativeCatalog_escapePairs_full readout))

private theorem fused_full_card_measurements :
    emptyCumulativeCounts.full = 2256 ∧
      observationCumulativeCounts.full = 136 ∧
      interventionCumulativeCounts.full = 44 ∧
      counterfactualCumulativeCounts.full = 0 := by
  exact ⟨empty_fused_full_eq_offDiagonal.trans unifiedOffDiagonalPairs_card,
    (singleton_fused_full_eq_escape_card ObsU).trans E_obs_card,
    (singleton_fused_full_eq_escape_card IntU).trans E_int_card,
    (singleton_fused_full_eq_escape_card CfU).trans E_cf_card⟩

private theorem cumulativeCatalog_agrees_iff
    (index : UnifiedCumulativeReadoutIndex) (left right : UnifiedBoolSCM) :
    (unifiedCumulativeCatalog.theoremAt index).primitives.agrees left right ↔
      match index with
      | .observation => ObsU left = ObsU right
      | .intervention => IntU left = IntU right
      | .counterfactual => CfU left = CfU right := by
  cases index <;> exact cumulativeReadoutBundle_agrees_iff _ left right

-- Section 43.1 causal fixed-catalog instance of CIRPT-IE-024, not its general law.
private theorem flat_observation_unique_zero :
    unifiedCumulativeCatalog.uniqueCaptureCount .observation = 0 := by
  unfold Catalog.uniqueCaptureCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair membership
  rcases Finset.mem_filter.mp membership with ⟨leaveOneOut, separated⟩
  have allAgreement := (unifiedCumulativeCatalog.indistinguishable_iff_forall
    (unifiedCumulativeCatalog.without .observation) pair.1 pair.2).1
      (Finset.mem_filter.mp leaveOneOut).2
  have intAgreement := allAgreement .intervention
    ((unifiedCumulativeCatalog.mem_without_iff .observation .intervention).2
      (by intro impossible; cases impossible))
  apply separated
  apply (cumulativeCatalog_agrees_iff .observation pair.1 pair.2).2
  exact unified_observation_intervention_strict_refinement.1 pair.1 pair.2
    ((cumulativeCatalog_agrees_iff .intervention pair.1 pair.2).1 intAgreement)

-- Section 43.1 causal fixed-catalog instance of CIRPT-IE-024, not its general law.
private theorem flat_intervention_unique_zero :
    unifiedCumulativeCatalog.uniqueCaptureCount .intervention = 0 := by
  unfold Catalog.uniqueCaptureCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair membership
  rcases Finset.mem_filter.mp membership with ⟨leaveOneOut, separated⟩
  have allAgreement := (unifiedCumulativeCatalog.indistinguishable_iff_forall
    (unifiedCumulativeCatalog.without .intervention) pair.1 pair.2).1
      (Finset.mem_filter.mp leaveOneOut).2
  have cfAgreement := allAgreement .counterfactual
    ((unifiedCumulativeCatalog.mem_without_iff .intervention .counterfactual).2
      (by intro impossible; cases impossible))
  apply separated
  apply (cumulativeCatalog_agrees_iff .intervention pair.1 pair.2).2
  exact unified_intervention_counterfactual_strict_refinement.1 pair.1 pair.2
    ((cumulativeCatalog_agrees_iff .counterfactual pair.1 pair.2).1 cfAgreement)

private theorem flat_counterfactual_unique_eq_L_cf :
    unifiedCumulativeCatalog.uniqueCapturePairs .counterfactual = L_cf := by
  apply Finset.ext
  intro pair
  simp only [Catalog.uniqueCapturePairs, Finset.mem_filter]
  constructor
  · rintro ⟨leaveOneOut, separated⟩
    rcases Finset.mem_filter.mp leaveOneOut with ⟨offDiagonal, agreement⟩
    have allAgreement := (unifiedCumulativeCatalog.indistinguishable_iff_forall
      (unifiedCumulativeCatalog.without .counterfactual) pair.1 pair.2).1 agreement
    have intAgreement := allAgreement .intervention
      ((unifiedCumulativeCatalog.mem_without_iff .counterfactual .intervention).2
        (by intro impossible; cases impossible))
    apply Finset.mem_filter.mpr
    exact ⟨(mem_unifiedOffDiagonalPairs_iff pair).2
        ((mem_arenaOffDiagonalPairs_iff pair).1 offDiagonal),
      (cumulativeCatalog_agrees_iff .intervention pair.1 pair.2).1 intAgreement,
      fun equalCf => separated
        ((cumulativeCatalog_agrees_iff .counterfactual pair.1 pair.2).2 equalCf)⟩
  · intro membership
    rcases Finset.mem_filter.mp membership with ⟨offDiagonal, equalInt, unequalCf⟩
    refine ⟨Finset.mem_filter.mpr ⟨(mem_arenaOffDiagonalPairs_iff pair).2
      ((mem_unifiedOffDiagonalPairs_iff pair).1 offDiagonal), ?_⟩, ?_⟩
    · apply (unifiedCumulativeCatalog.indistinguishable_iff_forall
        (unifiedCumulativeCatalog.without .counterfactual) pair.1 pair.2).2
      intro index membership
      have indexNotCf :=
        (unifiedCumulativeCatalog.mem_without_iff .counterfactual index).1 membership
      clear membership
      cases index with
      | observation =>
          apply (cumulativeCatalog_agrees_iff .observation pair.1 pair.2).2
          exact unified_observation_intervention_strict_refinement.1
            pair.1 pair.2 equalInt
      | intervention =>
          exact (cumulativeCatalog_agrees_iff .intervention pair.1 pair.2).2 equalInt
      | counterfactual => exact False.elim (indexNotCf rfl)
    · exact fun agreement => unequalCf
        ((cumulativeCatalog_agrees_iff .counterfactual pair.1 pair.2).1 agreement)

private theorem fused_unique_card_measurements :
    flatCumulativeCounts.unique .observation = 0 ∧
      flatCumulativeCounts.unique .intervention = 0 ∧
      flatCumulativeCounts.unique .counterfactual = 44 := by
  constructor
  · exact (unifiedCumulativeCatalog.fusedUnique_eq_uniqueCaptureCount
      unifiedStateEnumeration unifiedCumulativeIndexEnumeration .observation).trans
        flat_observation_unique_zero
  · constructor
    · exact (unifiedCumulativeCatalog.fusedUnique_eq_uniqueCaptureCount
        unifiedStateEnumeration unifiedCumulativeIndexEnumeration .intervention).trans
          flat_intervention_unique_zero
    · unfold flatCumulativeCounts
      calc
        (unifiedCumulativeCatalog.fusedCounts unifiedStateEnumeration
            unifiedCumulativeIndexEnumeration).unique .counterfactual =
            unifiedCumulativeCatalog.uniqueCaptureCount .counterfactual :=
          unifiedCumulativeCatalog.fusedUnique_eq_uniqueCaptureCount
            unifiedStateEnumeration unifiedCumulativeIndexEnumeration .counterfactual
        _ = (unifiedCumulativeCatalog.uniqueCapturePairs .counterfactual).card := rfl
        _ = L_cf.card := congrArg Finset.card flat_counterfactual_unique_eq_L_cf
        _ = 44 := cumulative_edge_card_measurements.2.2

-- T-034 branch-local escapes for the literal cumulative readouts.
example :
    (icEscapePairs ObsU).card = 80 ∧
      (icEscapePairs IntU).card = 20 ∧
      (icEscapePairs CfU).card = 0 ∧
      (oiEscapePairs ObsU).card = 56 ∧
      (oiEscapePairs IntU).card = 24 ∧
      (oiEscapePairs CfU).card = 0 := by
  exact ⟨ic_escape_card_measurements.1,
    ic_escape_card_measurements.2.1,
    ic_escape_card_measurements.2.2,
    oi_escape_card_measurements.1,
    oi_escape_card_measurements.2.1,
    oi_escape_card_measurements.2.2⟩

-- T-034 cumulative escape and edge-capture measurements.
example :
    emptyCumulativeCounts.full = 2256 ∧
      observationCumulativeCounts.full = 136 ∧
      interventionCumulativeCounts.full = 44 ∧
      counterfactualCumulativeCounts.full = 0 ∧
      unifiedOffDiagonalPairs.card = 2256 ∧ E_obs.card = 136 ∧
      E_int.card = 44 ∧ E_cf.card = 0 ∧
      L_obs.card = 2120 ∧ L_int.card = 92 ∧ L_cf.card = 44 ∧
      flatCumulativeCounts.unique .observation = 0 ∧
      flatCumulativeCounts.unique .intervention = 0 ∧
      flatCumulativeCounts.unique .counterfactual = 44 := by
  exact ⟨fused_full_card_measurements.1,
    fused_full_card_measurements.2.1,
    fused_full_card_measurements.2.2.1,
    fused_full_card_measurements.2.2.2,
    unifiedOffDiagonalPairs_card, E_obs_card, E_int_card, E_cf_card,
    cumulative_edge_card_measurements.1,
    cumulative_edge_card_measurements.2.1,
    cumulative_edge_card_measurements.2.2,
    fused_unique_card_measurements⟩

end D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalMeasurements
