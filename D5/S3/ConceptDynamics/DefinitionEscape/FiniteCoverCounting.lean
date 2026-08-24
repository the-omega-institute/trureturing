/- GID: D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite definition cuts cover residuals with diminishing capture and antitone escape. -/

import D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelReductionMeasure
import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Lattice

/- Library-search audit trail (2026-08-24):
   * Shape searches `rg -n 'Set \(X × X\)' D5/S3/ConceptDynamics` and
     `rg -n '⋃ |⋂ |iUnion|iInter|sUnion|biUnion'` over DefinitionEscape,
     Faithfulness, and Experiments found the canonical `defectRelation`,
     `conceptKernel`, `jointKernel`, and `blindResidual`; all are reused below.
     No second target residual, family kernel, cut-set, or counting-rate
     definition is introduced.
   * English searches for finite cover/cut set/sufficiency/blind kernel,
     marginal capture/gain/diminishing, counting weight, and escape-rate
     antitonicity found `FiniteAnchorCoverage.coveredInputs` and
     `BudgetedEscapeRateAntitone.budgeted_escape_rate_bounds_and_antitone`.
     `coveredInputs` unions finite anchor suites of arbitrary inputs and has no
     target residual or definition kernel, so it does not state clause one.
     The budget theorem's second conjunct is exactly clause four at a general
     weight; it is applied directly here to finite counting weight.
   * The neighboring `Experiments.experimentGain` is defined through that
     module's separate `targetDefects`, whereas this theory fixes
     `defectRelation` as the target-residual source. It is therefore not used
     to create a second route to the same residual proposition.
   * Chinese synonyms `有限覆盖|子覆盖|切集|定义集|充分|盲核|边际捕获|边际增益|
     递减|逃逸率|计数` and English family synonyms `joint|common|shared|indexed|
     family|union|intersection|kernel|readout` found no complete four-clause
     theorem beyond the reusable components above. `ls` and
     `git grep -n -E '^def |^  def |^noncomputable def ' --
     D5/S3/ConceptDynamics | head -60` supplied the neighboring vocabulary.
   * Pinned Mathlib searches found exact lemmas `Set.finite_subset_iUnion`,
     `Set.ncard_le_ncard`, `Set.compl_iInter`, and `Set.mem_iUnion`; the first
     two carry the finite extraction and counting monotonicity proofs.
   * Loogle queries for `Set.finite_subset_iUnion` and `Set.ncard_le_ncard`
     each returned that exact pinned-Mathlib declaration. The attempted
     LeanSearch `/api/search` endpoint returned HTTP 404. Reservoir was
     reachable as a package registry but exposed no theorem-level hit.
     `gh search code 'finite_subset_iUnion language:Lean'` found Mathlib and
     third-party uses in Matroid libraries, but no DECT residual-cover theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting

open D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelReductionMeasure
open D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- On a finite inhabited state space, all four finite-cover and counting
clauses hold. A definition's cut is the part of the canonical target defect
outside its imported `conceptKernel`. The second clause extracts a finite
subfamily from a full cover. The third specializes the imported blind-kernel
reduction measure to finite counting, and the fourth specializes the imported
budgeted escape-rate theorem to the same counting weight. -/
theorem finite_cover_counting
    {X C B Target Strategy : Type*} [Finite X] [Nonempty X]
    (Gamma Delta : Set (Concept X B)) (q : Concept X C)
    (target : Concept X Target) (d : Concept X B)
    (supplement : Strategy → Concept X B) (cost : Strategy → Real)
    (budget1 budget2 : Real) :
    let countingWeight : EscapeWeight (X × X) :=
      { mass := fun set => (set.ncard : Real)
        empty_mass := by simp
        mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
    (blindResidual Gamma q target = ∅ ↔
        (⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => item.1) definition)ᶜ) =
          defectRelation q target) ∧
      (blindResidual Gamma q target = ∅ →
        finiteSelectionSufficient Gamma q target) ∧
      (Gamma ⊆ Delta →
        blindKernelReductionMeasure
            (fun set : Set (X × X) => (set.ncard : Real))
            Delta q target d ≤
          blindKernelReductionMeasure
            (fun set : Set (X × X) => (set.ncard : Real))
            Gamma q target d) ∧
      ((defectRelation q target).Nonempty →
        (∃ strategy, cost strategy ≤ budget1) →
        budget1 ≤ budget2 →
        budgetedEscapeRate q supplement target cost countingWeight budget2 ≤
          budgetedEscapeRate q supplement target cost countingWeight budget1) := by
  letI := Fintype.ofFinite X
  dsimp only
  have coverCriterion :
      blindResidual Gamma q target = ∅ ↔
        (⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => item.1) definition)ᶜ) =
          defectRelation q target := by
    constructor
    · intro residualEmpty
      apply Set.Subset.antisymm
      · intro pair pairInUnion
        rcases Set.mem_iUnion.1 pairInUnion with ⟨definition, pairInCut⟩
        exact pairInCut.1
      · intro pair pairInResidual
        by_contra pairNotCovered
        have pairInJoint :
            pair ∈ jointKernel (fun item : Gamma => item.1) := by
          apply Set.mem_iInter.2
          intro definition
          by_contra pairNotInKernel
          apply pairNotCovered
          apply Set.mem_iUnion.2
          exact ⟨definition, pairInResidual, pairNotInKernel⟩
        have pairBlind : pair ∈ blindResidual Gamma q target :=
          ⟨pairInResidual, pairInJoint⟩
        rw [residualEmpty] at pairBlind
        exact pairBlind
    · intro coverEquality
      apply Set.eq_empty_iff_forall_notMem.2
      intro pair pairBlind
      have pairCovered :
          pair ∈ ⋃ definition : Gamma,
            defectRelation q target ∩
              (conceptKernel (fun item : Gamma => item.1) definition)ᶜ := by
        rw [coverEquality]
        exact pairBlind.1
      rcases Set.mem_iUnion.1 pairCovered with ⟨definition, pairInCut⟩
      have pairInKernel :
          pair ∈ conceptKernel (fun item : Gamma => item.1) definition :=
        Set.mem_iInter.1 pairBlind.2 definition
      exact pairInCut.2 pairInKernel
  refine ⟨coverCriterion, ?_, ?_, ?_⟩
  · intro residualEmpty
    have residualCover :
        defectRelation q target ⊆
          ⋃ definition : Gamma,
            defectRelation q target ∩
              (conceptKernel (fun item : Gamma => item.1) definition)ᶜ := by
      rw [(coverCriterion.mp residualEmpty)]
    rcases Set.finite_subset_iUnion (Set.toFinite (defectRelation q target))
        residualCover with ⟨selected, selectedFinite, selectedCover⟩
    letI : Fintype selected := selectedFinite.fintype
    let n := Fintype.card selected
    let definitions : Fin n → Gamma :=
      fun index => ((Fintype.equivFin selected).symm index).1
    have joinedDefectEmpty :
        defectRelation
            (languageExtension q (fun index => (definitions index).1)) target = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro pair pairInJoinedDefect
      have pairInBaselineDefect : pair ∈ defectRelation q target :=
        ⟨congrArg Prod.fst pairInJoinedDefect.1, pairInJoinedDefect.2⟩
      have pairCovered := selectedCover pairInBaselineDefect
      rcases Set.mem_iUnion.1 pairCovered with ⟨definition, pairCovered⟩
      rcases Set.mem_iUnion.1 pairCovered with
        ⟨definitionInSelected, pairInCut⟩
      let selectedDefinition : selected :=
        ⟨definition, definitionInSelected⟩
      let index : Fin n := Fintype.equivFin selected selectedDefinition
      have definitionAtIndex : definitions index = definition := by
        simp [definitions, index, selectedDefinition, n]
      have selectedEqual :
          (definitions index).1 pair.1 = (definitions index).1 pair.2 := by
        exact congrFun (congrArg Prod.snd pairInJoinedDefect.1) index
      have pairInKernel :
          pair ∈ conceptKernel (fun item : Gamma => item.1) definition := by
        change definition.1 pair.1 = definition.1 pair.2
        rw [← definitionAtIndex]
        exact selectedEqual
      exact pairInCut.2 pairInKernel
    rcases (target_recovery_criterion
        (languageExtension q (fun index => (definitions index).1)) target).2.2.1.mp
        joinedDefectEmpty with ⟨recover, recovery⟩
    exact ⟨n, definitions, recover, recovery⟩
  · intro gammaSubsetDelta
    unfold blindKernelReductionMeasure
    have capturedSubset :
        blindResidual Delta q target ∩
            ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ ⊆
          blindResidual Gamma q target ∩
            ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ := by
      rintro pair ⟨pairInDeltaResidual, pairSeparated⟩
      refine ⟨⟨pairInDeltaResidual.1, ?_⟩, pairSeparated⟩
      apply Set.mem_iInter.2
      intro definition
      let deltaDefinition : Delta :=
        ⟨definition.1, gammaSubsetDelta definition.2⟩
      have deltaEqual :=
        Set.mem_iInter.1 pairInDeltaResidual.2 deltaDefinition
      change deltaDefinition.1 pair.1 = deltaDefinition.1 pair.2 at deltaEqual
      change definition.1 pair.1 = definition.1 pair.2
      simpa only [deltaDefinition] using deltaEqual
    have countSubset := Set.ncard_le_ncard capturedSubset
    change
      ((blindResidual Delta q target ∩
        ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ).ncard :
          Real) ≤
        ((blindResidual Gamma q target ∩
          ({pair : X × X | Setoid.ker d pair.1 pair.2} : Set (X × X))ᶜ).ncard :
            Real)
    exact_mod_cast countSubset
  · intro baselineNonempty feasible budgetOrder
    let countingWeight : EscapeWeight (X × X) :=
      { mass := fun set => (set.ncard : Real)
        empty_mass := by simp
        mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
    change budgetedEscapeRate q supplement target cost countingWeight budget2 ≤
      budgetedEscapeRate q supplement target cost countingWeight budget1
    have baselineMassPositive :
        0 < countingWeight.mass (defectRelation q target) := by
      change 0 < ((defectRelation q target).ncard : Real)
      exact_mod_cast ((Set.ncard_pos (Set.toFinite _)).2 baselineNonempty)
    have escapeAtMostTotal : ∀ strategy,
        countingWeight.mass
            (defectRelation (conceptJoin q (supplement strategy)) target) ≤
          countingWeight.mass (defectRelation q target) := by
      intro strategy
      change
        ((defectRelation (conceptJoin q (supplement strategy)) target).ncard : Real) ≤
          ((defectRelation q target).ncard : Real)
      rw [residual_join_law]
      exact_mod_cast Set.ncard_le_ncard Set.inter_subset_left
    have valuesNonempty :
        (budgetedEscapeValues q supplement target cost countingWeight budget1).Nonempty := by
      rcases feasible with ⟨strategy, strategyFeasible⟩
      refine ⟨countingWeight.mass
          (defectRelation (conceptJoin q (supplement strategy)) target) /
            countingWeight.mass (defectRelation q target), strategy,
        strategyFeasible, rfl⟩
    exact (budgeted_escape_rate_bounds_and_antitone q supplement target cost
      countingWeight baselineMassPositive escapeAtMostTotal valuesNonempty).2
        budgetOrder

/- A single identity definition covers a genuinely nonempty Boolean target
residual and therefore admits a finite sufficient family. -/
example :
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    let Gamma : Set (Concept Bool Bool) := {id}
    (defectRelation q target).Nonempty ∧
      blindResidual Gamma q target = ∅ ∧
      finiteSelectionSufficient Gamma q target := by
  dsimp only
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  let Gamma : Set (Concept Bool Bool) := {id}
  have baselineNonempty : (defectRelation q target).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  have residualEmpty : blindResidual Gamma q target = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro pair pairBlind
    have identityInGamma : (id : Concept Bool Bool) ∈ Gamma := by
      exact Set.mem_singleton_iff.mpr rfl
    have pairInIdentityKernel :=
      Set.mem_iInter.1 pairBlind.2
        (⟨id, identityInGamma⟩ : Gamma)
    have pairEqual : pair.1 = pair.2 := by
      simpa [conceptKernel] using pairInIdentityKernel
    exact pairBlind.1.2 (congrArg target pairEqual)
  have package := finite_cover_counting Gamma Gamma q target id
    (fun _ : Unit => (id : Concept Bool Bool)) (fun _ => 0) 0 1
  exact ⟨baselineNonempty, residualEmpty, package.2.1 residualEmpty⟩

/- With no definitions, the same Boolean residual is not covered; this rules
out interpreting either sufficiency or the cut union as an unconditional fact. -/
example :
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    blindResidual (∅ : Set (Concept Bool Bool)) q target ≠ ∅ ∧
      (⋃ definition : (∅ : Set (Concept Bool Bool)),
        defectRelation q target ∩
          (conceptKernel
            (fun item : (∅ : Set (Concept Bool Bool)) => item.1)
            definition)ᶜ) ≠ defectRelation q target ∧
      ¬finiteSelectionSufficient
        (∅ : Set (Concept Bool Bool)) q target := by
  dsimp only
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  have residualNonempty :
      (blindResidual (∅ : Set (Concept Bool Bool)) q target).Nonempty :=
    ⟨(false, true), by
      simp [blindResidual, defectRelation, jointKernel, conceptKernel, target]⟩
  refine ⟨Set.nonempty_iff_ne_empty.mp residualNonempty, ?_, ?_⟩
  · intro coverEquality
    have pairCovered : (false, true) ∈
        ⋃ definition : (∅ : Set (Concept Bool Bool)),
          defectRelation q target ∩
            (conceptKernel
              (fun item : (∅ : Set (Concept Bool Bool)) => item.1)
              definition)ᶜ := by
      rw [coverEquality]
      exact ⟨rfl, Bool.false_ne_true⟩
    simp at pairCovered
  · exact ((blind_kernel_obstruction
      (∅ : Set (Concept Bool Bool)) q target).2 residualNonempty).2.2

/- Adding the identity definition exhausts the two captured ordered Boolean
pairs, so its next marginal capture is zero while the empty-family marginal is
strictly positive. -/
example :
    blindKernelReductionMeasure
        (fun set : Set (Bool × Bool) => (set.ncard : Real))
        ({(id : Concept Bool Bool)} : Set (Concept Bool Bool)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (id : Concept Bool Bool) = 0 ∧
      0 < blindKernelReductionMeasure
        (fun set : Set (Bool × Bool) => (set.ncard : Real))
        (∅ : Set (Concept Bool Bool)) (fun _ : Bool => ())
        (id : Concept Bool Bool) (id : Concept Bool Bool) := by
  have identityResidualEmpty :
      blindResidual ({(id : Concept Bool Bool)} : Set (Concept Bool Bool))
        (fun _ : Bool => ()) (id : Concept Bool Bool) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro pair pairBlind
    have pairInIdentityKernel :=
      Set.mem_iInter.1 pairBlind.2
        (⟨(id : Concept Bool Bool), Set.mem_singleton_iff.mpr rfl⟩ :
          ({(id : Concept Bool Bool)} : Set (Concept Bool Bool)))
    have pairEqual : pair.1 = pair.2 := by
      simpa [conceptKernel] using pairInIdentityKernel
    exact pairBlind.1.2 pairEqual
  constructor
  · rw [blindKernelReductionMeasure, identityResidualEmpty]
    simp
  · change 0 <
      ((blindResidual (∅ : Set (Concept Bool Bool))
          (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
        ({pair : Bool × Bool |
          Setoid.ker (id : Concept Bool Bool) pair.1 pair.2} :
            Set (Bool × Bool))ᶜ).ncard : Real)
    exact_mod_cast ((Set.ncard_pos (Set.toFinite _)).2
      ⟨(false, true), by
        simp [blindResidual, defectRelation, jointKernel, conceptKernel]⟩)

/- A zero-cost constant supplement leaves counting escape rate one, while the
unit-cost identity supplement makes rate one attain zero. Thus the certified
budget direction is strict here, and reversing it gives a false inequality. -/
example :
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    let supplement : Bool → Concept Bool Bool := fun
      | false => fun _ => false
      | true => id
    let cost : Bool → Real := fun
      | false => 0
      | true => 1
    let weight : EscapeWeight (Bool × Bool) :=
      { mass := fun set => (set.ncard : Real)
        empty_mass := by simp
        mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
    let rate := budgetedEscapeRate q supplement target cost weight
    (defectRelation q target).Nonempty ∧
      rate 0 = 1 ∧ rate 1 = 0 ∧ rate 1 < rate 0 ∧ ¬rate 0 ≤ rate 1 := by
  classical
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  let supplement : Bool → Concept Bool Bool := fun
    | false => fun _ => false
    | true => id
  let cost : Bool → Real := fun
    | false => 0
    | true => 1
  let weight : EscapeWeight (Bool × Bool) :=
    { mass := fun set => (set.ncard : Real)
      empty_mass := by simp
      mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
  let rate := budgetedEscapeRate q supplement target cost weight
  change (defectRelation q target).Nonempty ∧
    rate 0 = 1 ∧ rate 1 = 0 ∧ rate 1 < rate 0 ∧ ¬rate 0 ≤ rate 1
  have baselineEq :
      defectRelation q target = {(false, true), (true, false)} := by
    ext pair
    rcases pair with ⟨first, second⟩
    cases first <;> cases second <;> simp [q, target, defectRelation]
  have residualEq (strategy : Bool) :
      defectRelation (conceptJoin q (supplement strategy)) target =
        if strategy then ∅ else {(false, true), (true, false)} := by
    ext pair
    rcases pair with ⟨first, second⟩
    cases strategy <;> cases first <;> cases second <;>
      simp [q, target, supplement, defectRelation, conceptJoin]
  have baselineNonempty : (defectRelation q target).Nonempty := by
    rw [baselineEq]
    simp
  have valuesZero :
      budgetedEscapeValues q supplement target cost weight 0 = {(1 : Real)} := by
    ext value
    simp [budgetedEscapeValues, cost, residualEq, baselineEq, weight,
      eq_comm]
  have valuesOne :
      budgetedEscapeValues q supplement target cost weight 1 =
        {(0 : Real), (1 : Real)} := by
    ext value
    simp [budgetedEscapeValues, cost, residualEq, baselineEq, weight,
      eq_comm, or_comm]
  refine ⟨baselineNonempty, ?_⟩
  change
    sInf (budgetedEscapeValues q supplement target cost weight 0) = 1 ∧
      sInf (budgetedEscapeValues q supplement target cost weight 1) = 0 ∧
      sInf (budgetedEscapeValues q supplement target cost weight 1) <
        sInf (budgetedEscapeValues q supplement target cost weight 0) ∧
      ¬sInf (budgetedEscapeValues q supplement target cost weight 0) ≤
        sInf (budgetedEscapeValues q supplement target cost weight 1)
  rw [valuesZero, valuesOne]
  norm_num

#print axioms finite_cover_counting

end D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
