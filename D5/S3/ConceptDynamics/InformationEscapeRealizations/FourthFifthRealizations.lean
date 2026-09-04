/- GID: D5/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeRealizations/FourthFifthRealizations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete readouts bind contextual meanings and causal separation to typed laws. -/

import D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * Repository and pinned-Mathlib searches recorded in `FourthFifthArenas`
     found no legacy realization proofs for either frozen theorem.
   * The exact imported projections, `IsBinaryFixedMeaning`, `Int`, and `CF`
     are used as the concrete readouts, with the A2 Boolean admission lemma.
   * Backward proofs unfold only the realization slots and reconstruct the
     original statements without applying either frozen source theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations

open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas

namespace ContextRealization
open D5.S3.ConceptDynamics.Interpretation.InterpretationFixedPoint
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.ContextSource

private instance falseMeaningDecidable :
    DecidablePred (fun context : BinaryInterpretationContext =>
      IsBinaryFixedMeaning context (false, false, false)) := fun context => by
  unfold IsBinaryFixedMeaning
  infer_instance

private instance trueMeaningDecidable :
    DecidablePred (fun context : BinaryInterpretationContext =>
      IsBinaryFixedMeaning context (true, true, true)) := fun context => by
  unfold IsBinaryFixedMeaning
  infer_instance

def contextRealization : PrimitiveRealization contextSignature where
  readout
    | .text => fun context => context.text
    | .interpretationRule => fun context => context.interpretationRule
    | .readerAdmission => fun context => context.readerAdmission
    | .background => fun context => context.background
    | .evaluationGoal => fun context => context.evaluationGoal
    | .falseMeaning => fun context =>
        decide (IsBinaryFixedMeaning context (false, false, false))
    | .trueMeaning => fun context =>
        decide (IsBinaryFixedMeaning context (true, true, true))
  anchor
    | false => baselineContext
    | true => alternateContext

theorem context_parameters_can_select_distinct_fixed_points_realization :
    LegacyPrimitiveRealization contextArena
      (baselineContext.text = alternateContext.text ∧
        baselineContext.interpretationRule = alternateContext.interpretationRule ∧
        baselineContext.readerAdmission ≠ alternateContext.readerAdmission ∧
        baselineContext.background ≠ alternateContext.background ∧
        baselineContext.evaluationGoal ≠ alternateContext.evaluationGoal ∧
        IsBinaryFixedMeaning baselineContext (false, false, false) ∧
        IsBinaryFixedMeaning alternateContext (true, true, true) ∧
        (false, false, false) ≠ (true, true, true))
      contextRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨hText, hRule, hAdmission, hBackground, hGoal,
      hFalseMeaning, hTrueMeaning, hMeanings⟩
    dsimp [contextArena, contextRealization]
    exact ⟨hText, hRule, hAdmission, hBackground, hGoal,
      (admit_readout_eq_true_iff
        (fun context : BinaryInterpretationContext =>
          IsBinaryFixedMeaning context (false, false, false)) baselineContext).2 hFalseMeaning,
      (admit_readout_eq_true_iff
        (fun context : BinaryInterpretationContext =>
          IsBinaryFixedMeaning context (true, true, true)) alternateContext).2 hTrueMeaning,
      hMeanings⟩
  · intro hLaw
    dsimp [contextArena, contextRealization] at hLaw
    rcases hLaw with ⟨hText, hRule, hAdmission, hBackground, hGoal,
      hFalseMeaning, hTrueMeaning, hMeanings⟩
    exact ⟨hText, hRule, hAdmission, hBackground, hGoal,
      (admit_readout_eq_true_iff
        (fun context : BinaryInterpretationContext =>
          IsBinaryFixedMeaning context (false, false, false)) baselineContext).1 hFalseMeaning,
      (admit_readout_eq_true_iff
        (fun context : BinaryInterpretationContext =>
          IsBinaryFixedMeaning context (true, true, true)) alternateContext).1 hTrueMeaning,
      hMeanings⟩

example :
    letI : Fintype BinaryInterpretationContext := contextFintype
    letI : DecidableEq BinaryInterpretationContext := contextDecidableEq
    ((Finset.univ : Finset BinaryInterpretationContext).image fun context =>
      (context.readerAdmission, context.background, context.evaluationGoal)).card = 8 := by
  decide

example : letI : DecidableEq BinaryInterpretationContext := contextDecidableEq
    ¬contextRealization.toPrimitiveBundle.agrees baselineContext alternateContext := by
  letI : DecidableEq BinaryInterpretationContext := contextDecidableEq
  change ¬contextRealization.toPrimitiveBundle.agrees baselineContext alternateContext
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  intro agreement
  have admissionAgreement := agreement.1 ContextReadout.readerAdmission
  exact Bool.false_ne_true admissionAgreement

example : contextArena.toArena.Nondegenerate := by decide

end ContextRealization

namespace InterventionRealization
open D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open D5.S3.ConceptDynamics.InformationEscapeArenas.FourthFifthArenas.InterventionSource

def interventionRealization : PrimitiveRealization interventionSignature where
  readout
    | .intervention => Int
    | .counterfactual => CF
  anchor := fun index => Fin.elim0 index

theorem intervention_strictly_weaker_than_counterfactual_realization :
    LegacyPrimitiveRealization interventionArena
      (exists M N : DeterministicBoolSCM, Int M = Int N ∧ CF M ≠ CF N)
      interventionRealization := by
  refine ⟨?_⟩
  constructor
  · rintro ⟨M, N, interventions, counterfactuals⟩
    exact ⟨M, N, interventions, counterfactuals⟩
  · rintro ⟨M, N, interventions, counterfactuals⟩
    exact ⟨M, N, interventions, counterfactuals⟩

example :
    letI : Fintype DeterministicBoolSCM := modelFintype
    letI : DecidableEq DeterministicBoolSCM := modelDecidableEq
    ((Finset.univ : Finset DeterministicBoolSCM).image fun model =>
      (CF model false false false, CF model false false true,
        CF model true false false, CF model true false true)).card = 16 := by
  decide

example : letI : DecidableEq DeterministicBoolSCM := modelDecidableEq
    ¬interventionRealization.toPrimitiveBundle.agrees noEffectModel flipEffectModel := by
  letI : DecidableEq DeterministicBoolSCM := modelDecidableEq
  change ¬interventionRealization.toPrimitiveBundle.agrees noEffectModel flipEffectModel
  rw [PrimitiveRealization.toPrimitiveBundle_agrees_iff]
  intro agreement
  have cfAgreement := agreement.1 ModelReadout.counterfactual
  have pointAgreement := congrFun (congrFun (congrFun cfAgreement false) false) true
  exact Bool.false_ne_true pointAgreement

example : interventionArena.toArena.Nondegenerate := by decide

end InterventionRealization

end D5.S3.ConceptDynamics.InformationEscapeRealizations.FourthFifthRealizations
