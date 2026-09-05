/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/UnifiedCausalAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two frozen Boolean causal separations align faithfully on one cumulative 48-state coproduct. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
import D5.S3.ConceptDynamics.InformationEscapeArenas.ObservationIntervention
import D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

 /- Library-search audit trail (2026-09-05):
   * Exact repository hits `DeterministicBoolSCM`, `Obs`, `Int`, `CF`, and the
     four named witness models are reused from the two frozen separation modules.
   * Exact hits `collapse` and `intervention_eq_collapse_counterfactual` are
     imported from `CounterfactualKernelStrictlyFiner` and used in the second
     cumulative factorization.
   * `FourthFifthArenas.modelFintype/modelDecidableEq` and the global OI model
     instances from `InformationEscapeArenas.ObservationIntervention` supply the
     two finite branch carriers; no replacement instances are defined here.
   * Searches over `D5/S3/ConceptDynamics/InformationEscape*` found the landed
     `PrimitiveSignature`, `PrimitiveRealization`, `PrimitiveLawArena`, and
     `LegacyPrimitiveRealization` APIs but no unified causal coproduct owner.
   * Pinned Mathlib supplies finite coproduct and finite-function instances. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner

namespace IC

abbrev Model :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.DeterministicBoolSCM

abbrev Int :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.Int

abbrev CF :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.CF

abbrev noEffectModel :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.noEffectModel

abbrev flipEffectModel :=
  D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.flipEffectModel

end IC

namespace OI

abbrev Model :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.DeterministicBoolSCM

abbrev Obs :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Obs

abbrev Int :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.Int

abbrev xCausesYModel :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.xCausesYModel

abbrev yCausesXModel :=
  D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.yCausesXModel

end OI

abbrev UnifiedBoolSCM := IC.Model ⊕ OI.Model

 /-- The canonical 48-state coproduct of the two landed Boolean SCM carriers. -/
def unifiedArena : Arena := by
  letI : Fintype IC.Model :=
    D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelFintype
  letI : DecidableEq IC.Model :=
    D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.modelDecidableEq
  exact Arena.ofFintype UnifiedBoolSCM

abbrev ICObsTable := Bool → Nat
abbrev ICIntTable := Bool → Bool → Nat
abbrev ICCFTable := Bool → Bool → Bool → Bool
abbrev OIObsTable := Bool → Bool × Bool
abbrev OIIntTable := Bool → Bool → Bool × Bool

abbrev ObsOut := ICObsTable ⊕ OIObsTable
abbrev IntOut := ICIntTable ⊕ (OIObsTable × OIIntTable)
abbrev CfOut := ICCFTable ⊕ OI.Model

inductive UnifiedObservationInterventionReadout
  | observation
  | intervention
  deriving DecidableEq

instance : Fintype UnifiedObservationInterventionReadout where
  elems := {.observation, .intervention}
  complete := by intro index; cases index <;> simp

 /-- Branch-local observation/intervention slots on the unified carrier. -/
def unifiedObservationInterventionSignature :
    PrimitiveSignature UnifiedBoolSCM where
  Index := UnifiedObservationInterventionReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .observation => Option OIObsTable
    | .intervention => Option OIIntTable
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

 /-- The OI realization is injected into the right coproduct branch. -/
def observationInterventionUnifiedRealization :
    PrimitiveRealization unifiedObservationInterventionSignature where
  readout
    | .observation => fun
        | .inl _ => none
        | .inr model => some (OI.Obs model)
    | .intervention => fun
        | .inl _ => none
        | .inr model => some (OI.Int model)
  anchor := fun index => Fin.elim0 index

inductive UnifiedInterventionCounterfactualReadout
  | intervention
  | counterfactual
  deriving DecidableEq

instance : Fintype UnifiedInterventionCounterfactualReadout where
  elems := {.intervention, .counterfactual}
  complete := by intro index; cases index <;> simp

 /-- Branch-local intervention/counterfactual slots on the unified carrier. -/
def unifiedInterventionCounterfactualSignature :
    PrimitiveSignature UnifiedBoolSCM where
  Index := UnifiedInterventionCounterfactualReadout
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output
    | .intervention => Option ICIntTable
    | .counterfactual => Option ICCFTable
  outputDecidableEq := by intro i; cases i <;> infer_instance
  axis := fun _ => .cut
  readoutAxisNotAnchor := by simp
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

 /-- The IC realization is injected into the left coproduct branch. -/
def interventionCounterfactualUnifiedRealization :
    PrimitiveRealization unifiedInterventionCounterfactualSignature where
  readout
    | .intervention => fun
        | .inl model => some (IC.Int model)
        | .inr _ => none
    | .counterfactual => fun
        | .inl model => some (IC.CF model)
        | .inr _ => none
  anchor := fun index => Fin.elim0 index

 /-- The cumulative observation readout. -/
def ObsU : UnifiedBoolSCM → ObsOut
  | .inl model => .inl (IC.Int model false)
  | .inr model => .inr (OI.Obs model)

 /-- The cumulative intervention readout. -/
def IntU : UnifiedBoolSCM → IntOut
  | .inl model => .inl (IC.Int model)
  | .inr model => .inr (OI.Obs model, OI.Int model)

 /-- The cumulative counterfactual readout, literal on the OI branch. -/
def CfU : UnifiedBoolSCM → CfOut
  | .inl model => .inl (IC.CF model)
  | .inr model => .inr model

 /-- Forget the intervention coordinate down to observation. -/
def obsFromInt : IntOut → ObsOut
  | .inl table => .inl (table false)
  | .inr (observation, _) => .inr observation

 /-- Collapse counterfactual data down to intervention data. -/
def intFromCf : CfOut → IntOut
  | .inl table => .inl (collapse table)
  | .inr model => .inr (OI.Obs model, OI.Int model)

 /-- The observation readout factors through the intervention readout. -/
theorem obsU_factorization : ObsU = obsFromInt ∘ IntU := by
  funext model
  cases model <;> rfl

 /-- The intervention readout factors through the counterfactual readout. -/
theorem intU_factorization : IntU = intFromCf ∘ CfU := by
  funext model
  cases model with
  | inl source =>
      simp [IntU, CfU, intFromCf,
        intervention_eq_collapse_counterfactual source]
  | inr source => rfl

 /-- A concrete OI model whose observation differs from the named strictness witness. -/
def observationDistinctModel : OI.Model where
  direction := .xCausesY
  root := fun _ => false
  child := fun _ => false

 /-- Observation already captures one explicit ordered off-diagonal pair. -/
theorem unified_observation_positive_witness :
    (Sum.inr OI.xCausesYModel : UnifiedBoolSCM) ≠
        .inr observationDistinctModel ∧
      ObsU (.inr OI.xCausesYModel) ≠ ObsU (.inr observationDistinctModel) := by
  have readoutDifferent :
      ObsU (.inr OI.xCausesYModel) ≠ ObsU (.inr observationDistinctModel) := by
    intro equalReadout
    have equalAtTrue := congrFun (Sum.inr.inj equalReadout) true
    exact Bool.false_ne_true (congrArg Prod.fst equalAtTrue).symm
  exact ⟨fun equalModel => readoutDifferent (congrArg ObsU equalModel), readoutDifferent⟩

 /-- CAUSAL-IE-001. -/
theorem unified_observation_intervention_strict_refinement :
    (∀ M N : UnifiedBoolSCM, IntU M = IntU N → ObsU M = ObsU N) ∧
    (ObsU (.inr OI.xCausesYModel) = ObsU (.inr OI.yCausesXModel) ∧
      IntU (.inr OI.xCausesYModel) ≠ IntU (.inr OI.yCausesXModel)) := by
  constructor
  · intro M N equalIntervention
    rw [obsU_factorization]
    exact congrArg obsFromInt equalIntervention
  · constructor
    · rfl
    · intro equalIntervention
      have equalAtWitness := congrFun (congrFun
        (congrArg Prod.snd (Sum.inr.inj equalIntervention)) false) true
      exact Bool.false_ne_true (congrArg Prod.snd equalAtWitness)

 /-- CAUSAL-IE-002. -/
theorem unified_intervention_counterfactual_strict_refinement :
    (∀ M N : UnifiedBoolSCM, CfU M = CfU N → IntU M = IntU N) ∧
    (IntU (.inl IC.noEffectModel) = IntU (.inl IC.flipEffectModel) ∧
      CfU (.inl IC.noEffectModel) ≠ CfU (.inl IC.flipEffectModel)) := by
  constructor
  · intro M N equalCounterfactual
    rw [intU_factorization]
    exact congrArg intFromCf equalCounterfactual
  · constructor
    · apply congrArg Sum.inl
      funext treatment result
      cases treatment <;> cases result <;> rfl
    · intro equalCounterfactual
      have falseEqualsTrue :=
        congrFun (congrFun (congrFun (Sum.inl.inj equalCounterfactual) false) false) true
      change false = true at falseEqualsTrue
      exact Bool.false_ne_true falseEqualsTrue

 /-- The branch-local OI law lives on the common unified arena. -/
def observationInterventionLawArena : PrimitiveLawArena where
  toArena := unifiedArena
  signature := unifiedObservationInterventionSignature
  Law := fun realization => ∃ M N : OI.Model,
    realization.readout .observation (.inr M) =
        realization.readout .observation (.inr N) ∧
      realization.readout .intervention (.inr M) ≠
        realization.readout .intervention (.inr N)

 /-- The branch-local IC law lives on the common unified arena. -/
def interventionCounterfactualLawArena : PrimitiveLawArena where
  toArena := unifiedArena
  signature := unifiedInterventionCounterfactualSignature
  Law := fun realization => ∃ M N : IC.Model,
    realization.readout .intervention (.inl M) =
        realization.readout .intervention (.inl N) ∧
      realization.readout .counterfactual (.inl M) ≠
        realization.readout .counterfactual (.inl N)

 /-- The frozen OI theorem is faithfully transported by injection and restriction. -/
theorem observation_intervention_unified_realization :
    LegacyPrimitiveRealization observationInterventionLawArena
      (∃ M N : OI.Model, OI.Obs M = OI.Obs N ∧ OI.Int M ≠ OI.Int N)
      observationInterventionUnifiedRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨M, N, equalObservation, unequalIntervention⟩
    refine ⟨M, N, congrArg some equalObservation, ?_⟩
    change some (OI.Int M) ≠ some (OI.Int N)
    exact fun equalSome => unequalIntervention (Option.some.inj equalSome)
  · rintro ⟨M, N, equalObservation, unequalIntervention⟩
    refine ⟨M, N, Option.some.inj equalObservation, ?_⟩
    intro equalInt
    apply unequalIntervention
    exact congrArg some equalInt

 /-- The frozen IC theorem is faithfully transported by injection and restriction. -/
theorem intervention_counterfactual_unified_realization :
    LegacyPrimitiveRealization interventionCounterfactualLawArena
      (∃ M N : IC.Model, IC.Int M = IC.Int N ∧ IC.CF M ≠ IC.CF N)
      interventionCounterfactualUnifiedRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨M, N, equalIntervention, unequalCounterfactual⟩
    refine ⟨M, N, congrArg some equalIntervention, ?_⟩
    change some (IC.CF M) ≠ some (IC.CF N)
    exact fun equalSome => unequalCounterfactual (Option.some.inj equalSome)
  · rintro ⟨M, N, equalIntervention, unequalCounterfactual⟩
    refine ⟨M, N, Option.some.inj equalIntervention, ?_⟩
    intro equalCF
    apply unequalCounterfactual
    exact congrArg some equalCF

end D5.S3.ConceptDynamics.InformationEscapeRealizations.UnifiedCausalAlignment
