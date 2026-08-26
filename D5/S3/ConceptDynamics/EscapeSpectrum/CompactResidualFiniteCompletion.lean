/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/CompactResidualFiniteCompletion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/CompactResidualFiniteCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact open separation of every residual pair yields a zero-spectrum finite budget. -/

import D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
import Mathlib.Topology.Compactness.Compact

/- Library-search audit trail (2026-08-26):
   * Exact and semantic D5 searches for compact residual completion, finite
     subcovers, empty finite-selection defects, and zero finite escape spectra
     found no theorem covering this conclusion. `finite_cover_laws` is the
     closest hit: it identifies blind-kernel emptiness with the full cut cover,
     but its finite extraction assumes `Finite X` and does not provide a
     cost-matched budget or a zero escape-spectrum value.
   * `BudgetEnvelopeCompletion` supplies the canonical `finiteEscapeSpectrum`;
     this module proves that compact open residual separation gives an actual
     zero value at the cost of the extracted selection, rather than only an
     infimum or an `atTop` limit.
   * Pinned Mathlib contains the exact finite open-cover extractor
     `IsCompact.elim_finite_subcover`. Loogle query
     `IsCompact.elim_finite_subcover` returned that single declaration. A
     signature-shaped Loogle query failed to parse, the LeanSearch
     `/api/search` endpoint returned HTTP 404, and GitHub code search for
     `elim_finite_subcover language:Lean` returned Mathlib and downstream uses
     but no definition-escape residual theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EscapeSpectrum.CompactResidualFiniteCompletion

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- If the target-defect residual is compact, every candidate cut is open in
its residual subspace, and the common blind kernel is empty, then finitely many
candidates already remove the residual. With nonnegative candidate costs, the
sum of the selected costs is a nonnegative-real budget at which the canonical
finite escape spectrum is exactly zero. -/
theorem compact_residual_finite_completion
    {I X C Target : Type*} {V : I -> Type*}
    [TopologicalSpace (X × X)]
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I -> Real) (weight : EscapeWeight (X × X))
    (residualCompact : IsCompact (defectRelation q target))
    (blindKernelEmpty :
      defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅)
    (separationOpen : forall definition : Gamma,
      IsOpen {pair : {pair // pair ∈ defectRelation q target} |
        pair.1 ∉
          conceptKernel (fun item : Gamma => definitions item.1) definition})
    (candidateCostNonnegative : forall i, i ∈ Gamma -> 0 <= candidateCost i) :
    ∃ (selection : Finset Gamma) (budget : NNReal),
      (budget : Real) =
          finiteSelectionCost Gamma candidateCost selection /\
        defectRelation
            (conceptJoin q
              (finiteSelectionSupplement Gamma definitions selection)) target =
          ∅ /\
        finiteEscapeSpectrum Gamma definitions q target candidateCost weight
            budget = 0 := by
  classical
  let Cut : Gamma -> Set {pair // pair ∈ defectRelation q target} :=
    fun definition =>
      {pair | pair.1 ∉
        conceptKernel (fun item : Gamma => definitions item.1) definition}
  letI : CompactSpace {pair // pair ∈ defectRelation q target} :=
    isCompact_iff_compactSpace.mp residualCompact
  have fullCutCover :
      (⋃ definition : Gamma,
        defectRelation q target ∩
          (conceptKernel (fun item : Gamma => definitions item.1)
            definition)ᶜ) =
        defectRelation q target :=
    (finite_cover_laws Gamma definitions q target).1.mp blindKernelEmpty
  have residualCover :
      (Set.univ : Set {pair // pair ∈ defectRelation q target}) ⊆
        ⋃ definition : Gamma, Cut definition := by
    intro pair _pairInUniv
    have pairInAmbientCover : pair.1 ∈
        ⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => definitions item.1)
              definition)ᶜ := by
      rw [fullCutCover]
      exact pair.2
    rcases Set.mem_iUnion.1 pairInAmbientCover with
      ⟨definition, pairInCut⟩
    apply Set.mem_iUnion.2
    exact ⟨definition, pairInCut.2⟩
  obtain ⟨selection, selectionCovers⟩ :=
    isCompact_univ.elim_finite_subcover Cut separationOpen residualCover
  have selectedResidualEmpty :
      defectRelation
          (conceptJoin q
            (finiteSelectionSupplement Gamma definitions selection)) target =
        ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro pair pairInSelectedResidual
    have pairInBaselineResidual : pair ∈ defectRelation q target :=
      ⟨congrArg Prod.fst pairInSelectedResidual.1,
        pairInSelectedResidual.2⟩
    let residualPair : {pair // pair ∈ defectRelation q target} :=
      ⟨pair, pairInBaselineResidual⟩
    have pairCovered := selectionCovers (Set.mem_univ residualPair)
    rcases Set.mem_iUnion.1 pairCovered with ⟨definition, pairCovered⟩
    rcases Set.mem_iUnion.1 pairCovered with
      ⟨definitionInSelection, pairSeparated⟩
    have supplementEqual :
        finiteSelectionSupplement Gamma definitions selection pair.1 =
          finiteSelectionSupplement Gamma definitions selection pair.2 :=
      congrArg Prod.snd pairInSelectedResidual.1
    have selectedDefinitionEqual := congrFun supplementEqual definition
    have definitionValuesEqual :
        definitions definition.1 pair.1 = definitions definition.1 pair.2 := by
      simpa [finiteSelectionSupplement, definitionInSelection] using
        selectedDefinitionEqual
    apply pairSeparated
    exact definitionValuesEqual
  have selectionCostNonnegative :
      0 <= finiteSelectionCost Gamma candidateCost selection := by
    apply Finset.sum_nonneg
    intro item _itemInSelection
    exact candidateCostNonnegative item.1 item.2
  let budget : NNReal :=
    ⟨finiteSelectionCost Gamma candidateCost selection,
      selectionCostNonnegative⟩
  have budgetCost :
      (budget : Real) = finiteSelectionCost Gamma candidateCost selection :=
    rfl
  have budgetValuesBddBelow : BddBelow
      (finiteBudgetMassValues Gamma definitions q target candidateCost weight
        budget) := by
    refine ⟨0, ?_⟩
    rintro value ⟨candidate, _candidateFeasible, rfl⟩
    exact weight.mass_nonnegative _
  have selectionHasZeroMass :
      0 ∈ finiteBudgetMassValues Gamma definitions q target candidateCost
        weight budget := by
    refine ⟨selection, ?_, ?_⟩
    . change finiteSelectionCost Gamma candidateCost selection <= (budget : Real)
      exact budgetCost.ge
    . simp [finiteResidualMass, selectedResidualEmpty, weight.empty_mass]
  have envelopeNonnegative :
      0 <= finiteBudgetEnvelope Gamma definitions q target candidateCost weight
        budget := by
    change 0 <= sInf
      (finiteBudgetMassValues Gamma definitions q target candidateCost weight
        budget)
    refine (le_csInf_iff budgetValuesBddBelow
      ⟨0, selectionHasZeroMass⟩).2 ?_
    rintro value ⟨candidate, _candidateFeasible, rfl⟩
    exact weight.mass_nonnegative _
  have envelopeAtMostZero :
      finiteBudgetEnvelope Gamma definitions q target candidateCost weight
          budget <= 0 := by
    change sInf
      (finiteBudgetMassValues Gamma definitions q target candidateCost weight
        budget) <= 0
    exact csInf_le budgetValuesBddBelow selectionHasZeroMass
  have envelopeZero :
      finiteBudgetEnvelope Gamma definitions q target candidateCost weight
          budget = 0 :=
    le_antisymm envelopeAtMostZero envelopeNonnegative
  refine ⟨selection, budget, budgetCost, selectedResidualEmpty, ?_⟩
  simp [finiteEscapeSpectrum, envelopeZero]

/- The residual domain used above can be inhabited: a constant readout misses
the two off-diagonal Boolean pairs distinguished by the identity target. -/
example : Nonempty
    {pair // pair ∈
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool)} := by
  refine ⟨(false, true), ?_⟩
  simp [defectRelation]

/- All theorem hypotheses are jointly satisfiable on a nonempty residual: one
Boolean identity candidate separates both pairs missed by a constant readout. -/
example :
    let Gamma : Set Unit := Set.univ
    let definitions : forall _ : Unit, Concept Bool Bool := fun _ => id
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    let candidateCost : Unit -> Real := fun _ => 1
    IsCompact (defectRelation q target) /\
      defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ /\
      (forall definition : Gamma,
        IsOpen {pair : {pair // pair ∈ defectRelation q target} |
          pair.1 ∉
            conceptKernel (fun item : Gamma => definitions item.1)
              definition}) /\
      (forall i, i ∈ Gamma -> 0 <= candidateCost i) := by
  dsimp only
  refine ⟨(Set.toFinite _).isCompact, ?_, ?_, ?_⟩
  . ext pair
    rcases pair with ⟨left, right⟩
    simp [defectRelation, jointKernel, conceptKernel]
  . intro definition
    exact isOpen_discrete _
  . intro i _iInGamma
    norm_num

#print axioms compact_residual_finite_completion

end D5.S3.ConceptDynamics.EscapeSpectrum.CompactResidualFiniteCompletion
