/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/BudgetEnvelopeCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite residual masses and nonnegative budget layers have the same infimum and limit. -/

import D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

/- Library-search audit trail (2026-08-26):
   * Exact and semantic searches for `budget_envelope_infimum_and_limit`,
     budget envelopes, infinite budgets, escape spectra, and an `atTop` limit
     of budgeted `sInf` values found no covering declaration in `D5`.
   * The closest repository hit is
     `BudgetedEscapeRateAntitone.budgeted_escape_rate_bounds_and_antitone`.
     It supplies pointwise bounds and budget antitonicity for arbitrary
     strategies, but no infimum over all budgets, cofinal finite-family
     identity, or infinite-budget limit.
   * `FiniteCoverCounting` supplies the canonical `finiteSelectionSupplement`
     and `finiteSelectionCost`; this module reuses both rather than introducing
     a second finite-family or cost semantics.
   * Pinned Mathlib exact hits `csInf_le_csInf`, `le_csInf_iff`, `csInf_le`,
     `isGLB_csInf`, and `tendsto_atTop_isGLB` provide the order and convergence
     steps. No optimizer or infimum-attainment theorem is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion

open Filter
open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- The residual mass left by one finite family of candidate definitions. -/
def finiteResidualMass
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (weight : EscapeWeight (X × X)) (selection : Finset Gamma) : Real :=
  weight.mass
    (defectRelation
      (conceptJoin q (finiteSelectionSupplement Gamma definitions selection))
      target)

/-- Residual masses of the finite families affordable at a nonnegative budget. -/
def finiteBudgetMassValues
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I -> Real) (weight : EscapeWeight (X × X))
    (budget : NNReal) : Set Real :=
  finiteResidualMass Gamma definitions q target weight ''
    {selection |
      finiteSelectionCost Gamma candidateCost selection <= (budget : Real)}

/-- The unnormalized budget envelope of finite residual masses. -/
noncomputable def finiteBudgetEnvelope
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I -> Real) (weight : EscapeWeight (X × X))
    (budget : NNReal) : Real :=
  sInf (finiteBudgetMassValues
    Gamma definitions q target candidateCost weight budget)

/-- The budget envelope normalized by the baseline target-defect mass. -/
noncomputable def finiteEscapeSpectrum
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I -> Real) (weight : EscapeWeight (X × X))
    (budget : NNReal) : Real :=
  finiteBudgetEnvelope Gamma definitions q target candidateCost weight budget /
    weight.mass (defectRelation q target)

/-- The infimum residual mass over all finite candidate families. -/
noncomputable def allFiniteResidualInfimum
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (weight : EscapeWeight (X × X)) : Real :=
  sInf (Set.range (finiteResidualMass Gamma definitions q target weight))

/-- Nonnegative budget layers are cofinal among all finite candidate families.
Consequently their envelope is antitone, stays between zero and the positive
baseline mass, and has the same infimum and `atTop` limit as all finite
residual masses. Division by the positive baseline preserves both conclusions.
No finite family is asserted to attain either infimum. -/
theorem budget_envelope_infimum_and_limit
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I -> Real) (weight : EscapeWeight (X × X))
    (baselineMassPositive : 0 < weight.mass (defectRelation q target))
    (massMonotone : Monotone weight.mass) :
    Antitone
        (finiteBudgetEnvelope
          Gamma definitions q target candidateCost weight) /\
      (forall budget,
        0 <= finiteBudgetEnvelope
              Gamma definitions q target candidateCost weight budget /\
          finiteBudgetEnvelope
              Gamma definitions q target candidateCost weight budget <=
            weight.mass (defectRelation q target)) /\
      sInf (Set.range (finiteBudgetEnvelope
          Gamma definitions q target candidateCost weight)) =
        allFiniteResidualInfimum Gamma definitions q target weight /\
      Tendsto
        (finiteBudgetEnvelope
          Gamma definitions q target candidateCost weight)
        atTop
        (nhds (allFiniteResidualInfimum Gamma definitions q target weight)) /\
      sInf (Set.range (finiteEscapeSpectrum
          Gamma definitions q target candidateCost weight)) =
        allFiniteResidualInfimum Gamma definitions q target weight /
          weight.mass (defectRelation q target) /\
      Tendsto
        (finiteEscapeSpectrum
          Gamma definitions q target candidateCost weight)
        atTop
        (nhds
          (allFiniteResidualInfimum Gamma definitions q target weight /
            weight.mass (defectRelation q target))) := by
  classical
  let mass : Finset Gamma -> Real :=
    finiteResidualMass Gamma definitions q target weight
  let values : NNReal -> Set Real :=
    finiteBudgetMassValues Gamma definitions q target candidateCost weight
  let envelope : NNReal -> Real :=
    finiteBudgetEnvelope Gamma definitions q target candidateCost weight
  let spectrum : NNReal -> Real :=
    finiteEscapeSpectrum Gamma definitions q target candidateCost weight
  let baseline : Real := weight.mass (defectRelation q target)
  let globalInf : Real :=
    allFiniteResidualInfimum Gamma definitions q target weight
  have massNonnegative (selection : Finset Gamma) : 0 <= mass selection := by
    exact weight.mass_nonnegative _
  have residualSubsetBaseline (selection : Finset Gamma) :
      defectRelation
          (conceptJoin q
            (finiteSelectionSupplement Gamma definitions selection)) target <=
        defectRelation q target := by
    rintro pair pairInResidual
    exact ⟨congrArg Prod.fst pairInResidual.1, pairInResidual.2⟩
  have residualAtMostBaseline (selection : Finset Gamma) :
      mass selection <= baseline := by
    exact massMonotone (residualSubsetBaseline selection)
  have massRangeBddBelow : BddBelow (Set.range mass) := by
    refine ⟨0, ?_⟩
    rintro value ⟨selection, rfl⟩
    exact massNonnegative selection
  have valuesBddBelow (budget : NNReal) : BddBelow (values budget) := by
    refine ⟨0, ?_⟩
    rintro value ⟨selection, _feasible, rfl⟩
    exact massNonnegative selection
  have valuesNonempty (budget : NNReal) : (values budget).Nonempty := by
    refine ⟨mass ∅, ∅, ?_, rfl⟩
    change (0 : Real) <= (budget : Real)
    exact budget.coe_nonneg
  have envelopeAntitone : Antitone envelope := by
    intro budget1 budget2 budgetOrder
    change sInf (values budget2) <= sInf (values budget1)
    apply csInf_le_csInf (valuesBddBelow budget2) (valuesNonempty budget1)
    rintro value ⟨selection, feasible, rfl⟩
    change finiteSelectionCost Gamma candidateCost selection <=
      (budget1 : Real) at feasible
    refine ⟨selection, ?_, rfl⟩
    change finiteSelectionCost Gamma candidateCost selection <=
      (budget2 : Real)
    exact feasible.trans (by exact_mod_cast budgetOrder)
  have envelopeBounds (budget : NNReal) :
      0 <= envelope budget /\ envelope budget <= baseline := by
    constructor
    · change 0 <= sInf (values budget)
      refine (le_csInf_iff (valuesBddBelow budget) (valuesNonempty budget)).2 ?_
      rintro value ⟨selection, _feasible, rfl⟩
      exact massNonnegative selection
    · change sInf (values budget) <= baseline
      rcases valuesNonempty budget with ⟨value, valueMem⟩
      exact (csInf_le (valuesBddBelow budget) valueMem).trans (by
        rcases valueMem with ⟨selection, _feasible, rfl⟩
        exact residualAtMostBaseline selection)
  have globalInfLowerEnvelope (budget : NNReal) :
      globalInf <= envelope budget := by
    change sInf (Set.range mass) <= sInf (values budget)
    refine (le_csInf_iff (valuesBddBelow budget) (valuesNonempty budget)).2 ?_
    rintro value ⟨selection, _feasible, rfl⟩
    exact csInf_le massRangeBddBelow ⟨selection, rfl⟩
  have envelopeCofinal (selection : Finset Gamma) :
      exists budget : NNReal, envelope budget <= mass selection := by
    let budget : NNReal :=
      ⟨max (finiteSelectionCost Gamma candidateCost selection) 0,
        le_max_right _ _⟩
    refine ⟨budget, ?_⟩
    change sInf (values budget) <= mass selection
    apply csInf_le (valuesBddBelow budget)
    refine ⟨selection, ?_, rfl⟩
    change finiteSelectionCost Gamma candidateCost selection <=
      max (finiteSelectionCost Gamma candidateCost selection) 0
    exact le_max_left _ _
  have envelopeRangeBddBelow : BddBelow (Set.range envelope) := by
    refine ⟨globalInf, ?_⟩
    rintro value ⟨budget, rfl⟩
    exact globalInfLowerEnvelope budget
  have envelopeInfimumEq : sInf (Set.range envelope) = globalInf := by
    apply le_antisymm
    · refine (le_csInf_iff massRangeBddBelow (Set.range_nonempty mass)).2 ?_
      intro value valueMem
      rcases valueMem with ⟨selection, rfl⟩
      obtain ⟨budget, envelopeLe⟩ := envelopeCofinal selection
      exact (csInf_le envelopeRangeBddBelow ⟨budget, rfl⟩).trans envelopeLe
    · refine (le_csInf_iff envelopeRangeBddBelow
        (Set.range_nonempty envelope)).2 ?_
      intro value valueMem
      rcases valueMem with ⟨budget, rfl⟩
      exact globalInfLowerEnvelope budget
  have envelopeTendsto : Tendsto envelope atTop (nhds globalInf) := by
    apply tendsto_atTop_isGLB envelopeAntitone
    rw [← envelopeInfimumEq]
    exact isGLB_csInf (Set.range_nonempty envelope) envelopeRangeBddBelow
  have spectrumEq : spectrum = fun budget => envelope budget / baseline := by
    rfl
  have spectrumAntitone : Antitone spectrum := by
    rw [spectrumEq]
    intro budget1 budget2 budgetOrder
    exact div_le_div_of_nonneg_right
      (envelopeAntitone budgetOrder) baselineMassPositive.le
  have spectrumTendsto :
      Tendsto spectrum atTop (nhds (globalInf / baseline)) := by
    rw [spectrumEq]
    exact envelopeTendsto.div_const baseline
  have spectrumInfimumEq :
      sInf (Set.range spectrum) = globalInf / baseline := by
    exact (isGLB_of_tendsto_atTop spectrumAntitone spectrumTendsto).csInf_eq
      (Set.range_nonempty spectrum)
  change Antitone envelope /\
    (forall budget, 0 <= envelope budget /\ envelope budget <= baseline) /\
    sInf (Set.range envelope) = globalInf /\
    Tendsto envelope atTop (nhds globalInf) /\
    sInf (Set.range spectrum) = globalInf / baseline /\
    Tendsto spectrum atTop (nhds (globalInf / baseline))
  exact ⟨envelopeAntitone, envelopeBounds, envelopeInfimumEq,
    envelopeTendsto, spectrumInfimumEq, spectrumTendsto⟩

#print axioms budget_envelope_infimum_and_limit

end D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
