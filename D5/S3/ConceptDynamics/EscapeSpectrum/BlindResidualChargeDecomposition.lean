/- GID: D5/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/EscapeSpectrum/BlindResidualChargeDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite residual splits into its blind and finitely removable charge. -/

import D5.S3.ConceptDynamics.EscapeSpectrum.BudgetEnvelopeCompletion
import Mathlib.MeasureTheory.Measure.AddContent

/- Library-search audit trail (2026-08-26):
   * Exact and semantic D5 searches for blind-residual charge decompositions,
     finite-additive blind mass, and a joint-kernel subset of every finite
     selected residual found no covering declaration. `finite_cover_laws` is
     the closest set-theoretic result, but it characterizes when the blind
     residual is empty and neither proves the general subset nor measures it.
   * `BlindKernelReductionMeasure` assigns a nonnegative weight to pairs
     removed by one new definition. It assumes no additivity and does not split
     an arbitrary finite selected residual around the common blind kernel.
   * The canonical `defectRelation`, `conceptKernel`, `jointKernel`, and
     `finiteSelectionSupplement` are reused. Pinned Mathlib's `IsSetRing` and
     `AddContent` give the source's set algebra and finitely additive charge
     without specializing the algebra to the full powerset.
   * Pinned Mathlib searches found `addContent_union`, `addContent_mono`,
     `Set.union_sdiff_cancel`, and `Set.disjoint_sdiff_right`, which supply the
     exact finite-additivity split and its monotonicity consequence.
     Loogle returned those declarations but no theorem for the full residual
     statement. LeanSearch's `/api/search` endpoint returned HTTP 404, and
     GitHub code search found no definition-escape charge decomposition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.EscapeSpectrum.BlindResidualChargeDecomposition

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open MeasureTheory

/-- For a finite selection from a countable definition language, the common
blind residual is the baseline residual outside all single-definition cuts and
is contained in the selected residual. A finitely additive nonnegative charge
therefore splits the selected residual exactly into blind mass and the mass
still removable by other definitions. The statement also records the source's
degenerate convention: an empty language leaves the baseline residual
unchanged. -/
theorem blind_residual_charge_decomposition
    {I X C Target : Type*} {V : I -> Type*}
    (Gamma : Set I) (definitions : forall i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I -> Real) (budget : NNReal)
    (selection : Finset Gamma)
    (setAlgebra : Set (Set (X × X)))
    (setAlgebraRing : IsSetRing setAlgebra)
    (charge : AddContent NNReal setAlgebra)
    (_languageCountable : Gamma.Countable)
    (_candidateCostPositive : forall i, i ∈ Gamma -> 0 < candidateCost i)
    (_budgetNonnegative : 0 <= (budget : Real))
    (_baselineMassPositive : 0 < charge (defectRelation q target))
    (residualMem : defectRelation q target ∈ setAlgebra)
    (blindMem :
      defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) ∈
        setAlgebra)
    (cutMem : forall definition : Gamma,
      defectRelation q target ∩
          (conceptKernel (fun item : Gamma => definitions item.1)
            definition)ᶜ ∈
        setAlgebra) :
    let residual := defectRelation q target
    let restrictedDefinitions : forall item : Gamma, Concept X (V item.1) :=
      fun item => definitions item.1
    let blind := residual ∩ jointKernel restrictedDefinitions
    let cut : Gamma -> Set (X × X) := fun definition =>
      residual ∩ (conceptKernel restrictedDefinitions definition)ᶜ
    let selectedResidual :=
      defectRelation
        (conceptJoin q
          (finiteSelectionSupplement Gamma definitions selection)) target
    blind = residual \ ⋃ definition : Gamma, cut definition /\
      selectedResidual =
        residual \ ⋃ definition ∈ selection, cut definition /\
      blind ⊆ selectedResidual /\
      selectedResidual ∈ setAlgebra /\
      charge blind <= charge selectedResidual /\
      charge selectedResidual =
        charge blind + charge (selectedResidual \ blind) /\
      (Gamma = ∅ -> selectedResidual = residual) := by
  classical
  dsimp only
  let restrictedDefinitions : forall item : Gamma, Concept X (V item.1) :=
    fun item => definitions item.1
  let residual : Set (X × X) := defectRelation q target
  let blind : Set (X × X) := residual ∩ jointKernel restrictedDefinitions
  let cut : Gamma -> Set (X × X) := fun definition =>
    residual ∩ (conceptKernel restrictedDefinitions definition)ᶜ
  let selectedResidual : Set (X × X) :=
    defectRelation
      (conceptJoin q
        (finiteSelectionSupplement Gamma definitions selection)) target
  have blindAsComplement : blind = residual \ ⋃ definition : Gamma, cut definition := by
    apply Set.Subset.antisymm
    · intro pair pairBlind
      refine ⟨pairBlind.1, ?_⟩
      intro pairCovered
      rcases Set.mem_iUnion.1 pairCovered with
        ⟨definition, pairInCut⟩
      have pairInKernel : pair ∈
          conceptKernel restrictedDefinitions definition :=
        Set.mem_iInter.1 pairBlind.2 definition
      exact pairInCut.2 pairInKernel
    · intro pair pairOutsideCuts
      refine ⟨pairOutsideCuts.1, Set.mem_iInter.2 ?_⟩
      intro definition
      by_contra pairOutsideKernel
      apply pairOutsideCuts.2
      apply Set.mem_iUnion.2
      exact ⟨definition, pairOutsideCuts.1, pairOutsideKernel⟩
  have selectedAsComplement :
      selectedResidual =
        residual \ ⋃ definition ∈ selection, cut definition := by
    apply Set.Subset.antisymm
    · intro pair pairSelected
      refine ⟨⟨congrArg Prod.fst pairSelected.1, pairSelected.2⟩, ?_⟩
      intro pairCovered
      rcases Set.mem_iUnion.1 pairCovered with
        ⟨definition, pairCovered⟩
      rcases Set.mem_iUnion.1 pairCovered with
        ⟨definitionSelected, pairInCut⟩
      have supplementEqual := congrArg Prod.snd pairSelected.1
      change
        finiteSelectionSupplement Gamma definitions selection pair.1 =
          finiteSelectionSupplement Gamma definitions selection pair.2 at supplementEqual
      have selectedDefinitionEqual := congrFun supplementEqual definition
      have definitionValuesEqual :
          definitions definition.1 pair.1 =
            definitions definition.1 pair.2 := by
        simpa [finiteSelectionSupplement, definitionSelected] using selectedDefinitionEqual
      exact pairInCut.2 definitionValuesEqual
    · intro pair pairOutsideSelectedCuts
      refine ⟨?_, pairOutsideSelectedCuts.1.2⟩
      apply Prod.ext
      · exact pairOutsideSelectedCuts.1.1
      · change
          finiteSelectionSupplement Gamma definitions selection pair.1 =
            finiteSelectionSupplement Gamma definitions selection pair.2
        funext definition
        by_cases definitionSelected : definition ∈ selection
        · have pairInKernel : pair ∈
              conceptKernel restrictedDefinitions definition := by
            by_contra pairOutsideKernel
            apply pairOutsideSelectedCuts.2
            apply Set.mem_iUnion.2
            refine ⟨definition, Set.mem_iUnion.2 ?_⟩
            exact ⟨definitionSelected, pairOutsideSelectedCuts.1,
              pairOutsideKernel⟩
          simp only [finiteSelectionSupplement, definitionSelected, if_pos,
            Option.some.injEq]
          exact pairInKernel
        · simp [finiteSelectionSupplement, definitionSelected]
  have blindSubsetSelected : blind ⊆ selectedResidual := by
    intro pair pairBlind
    refine ⟨?_, pairBlind.1.2⟩
    apply Prod.ext
    · exact pairBlind.1.1
    · change
        finiteSelectionSupplement Gamma definitions selection pair.1 =
          finiteSelectionSupplement Gamma definitions selection pair.2
      funext definition
      by_cases definitionSelected : definition ∈ selection
      · simp only [finiteSelectionSupplement, definitionSelected, if_pos,
          Option.some.injEq]
        exact Set.mem_iInter.1 pairBlind.2 definition
      · simp [finiteSelectionSupplement, definitionSelected]
  have selectedCutUnionMem :
      (⋃ definition ∈ selection, cut definition) ∈ setAlgebra := by
    apply setAlgebraRing.biUnion_mem selection
    intro definition _definitionSelected
    exact cutMem definition
  have selectedResidualMem : selectedResidual ∈ setAlgebra := by
    rw [selectedAsComplement]
    exact setAlgebraRing.sdiff_mem residualMem selectedCutUnionMem
  have blindMassLeSelected : charge blind <= charge selectedResidual := by
    exact addContent_mono setAlgebraRing.isSetSemiring blindMem
      selectedResidualMem blindSubsetSelected
  have chargeDecomposition :
      charge selectedResidual =
        charge blind + charge (selectedResidual \ blind) := by
    have selectedDifferenceMem : selectedResidual \ blind ∈ setAlgebra :=
      setAlgebraRing.sdiff_mem selectedResidualMem blindMem
    have additiveSplit := addContent_union (m := charge) setAlgebraRing blindMem
      selectedDifferenceMem Set.disjoint_sdiff_right
    rwa [Set.union_sdiff_cancel blindSubsetSelected] at additiveSplit
  have emptyLanguageResidual : Gamma = ∅ -> selectedResidual = residual := by
    intro languageEmpty
    apply Set.Subset.antisymm
    · intro pair pairSelected
      exact ⟨congrArg Prod.fst pairSelected.1, pairSelected.2⟩
    · intro pair pairResidual
      refine ⟨?_, pairResidual.2⟩
      apply Prod.ext
      · exact pairResidual.1
      · funext definition
        have impossible : definition.1 ∈ (∅ : Set I) := by
          simpa [languageEmpty] using definition.2
        simp at impossible
  exact ⟨blindAsComplement, selectedAsComplement, blindSubsetSelected,
    selectedResidualMem, blindMassLeSelected, chargeDecomposition,
    emptyLanguageResidual⟩

/- The residual domain is genuinely inhabited: a constant Boolean readout
misses the two off-diagonal pairs distinguished by the identity target. -/
example : Nonempty
    {pair // pair ∈
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool)} := by
  refine ⟨(false, true), ?_⟩
  simp [defectRelation]

/- The countability, nonempty-language, positive-cost, set-algebra, and
positive finite-charge conditions are jointly satisfiable by counting mass. -/
example :
    let Gamma : Set Unit := Set.univ
    let candidateCost : Unit -> Real := fun _ => 1
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    Gamma.Countable /\ Gamma.Nonempty /\
      (forall i, i ∈ Gamma -> 0 < candidateCost i) /\
      ∃ (budget : NNReal) (_selection : Finset Gamma)
          (setAlgebra : Set (Set (Bool × Bool)))
          (charge : AddContent NNReal setAlgebra),
        0 <= (budget : Real) /\
          IsSetRing setAlgebra /\
          0 < charge (defectRelation q target) /\
          defectRelation q target ∈ setAlgebra /\
          defectRelation q target ∩
              jointKernel
                (fun _ : Gamma => (id : Concept Bool Bool)) ∈
            setAlgebra /\
          (forall definition : Gamma,
            defectRelation q target ∩
                (conceptKernel
                  (fun _ : Gamma => (id : Concept Bool Bool)) definition)ᶜ ∈
              setAlgebra) := by
  dsimp only
  let setAlgebra : Set (Set (Bool × Bool)) := Set.univ
  have setAlgebraRing : IsSetRing setAlgebra :=
    { empty_mem := Set.mem_univ _
      union_mem := fun {_ _} _ _ => Set.mem_univ _
      sdiff_mem := fun {_ _} _ _ => Set.mem_univ _ }
  let charge : AddContent NNReal setAlgebra :=
    setAlgebraRing.addContent_of_union
      (fun set => (set.ncard : NNReal)) (by simp) (by
        intro left right _leftMem _rightMem disjoint
        exact_mod_cast Set.ncard_union_eq disjoint)
  have baselineEq :
      defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) =
        {(false, true), (true, false)} := by
    ext pair
    rcases pair with ⟨first, second⟩
    cases first <;> cases second <;> simp [defectRelation]
  refine ⟨(Set.toFinite _).countable, Set.univ_nonempty, ?_,
    0, ∅, setAlgebra, charge, by norm_num, setAlgebraRing, ?_,
    Set.mem_univ _, Set.mem_univ _, ?_⟩
  · intro i _iInGamma
    norm_num
  · rw [baselineEq]
    change 0 < (({(false, true), (true, false)} : Set (Bool × Bool)).ncard : NNReal)
    rw [Set.ncard_pair (by decide)]
    norm_num
  · intro definition
    exact Set.mem_univ _

#print axioms blind_residual_charge_decomposition

end D5.S3.ConceptDynamics.EscapeSpectrum.BlindResidualChargeDecomposition
