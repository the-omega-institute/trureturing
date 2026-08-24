/- GID: D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite definition cuts cover residuals with diminishing capture and antitone escape. -/

import D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
import D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Lattice

/- Library-search audit trail (2026-08-24):
   * Shape searches `rg -n 'Set \(X × X\)' D5/S3/ConceptDynamics` and
     `rg -n '⋃ |⋂ |iUnion|iInter|sUnion|biUnion'` over DefinitionEscape,
     Faithfulness, and Experiments found the canonical `defectRelation`,
     `conceptKernel` and the dependent `jointKernel`; both are reused below.
     The blind part is written directly as the canonical target defect
     intersected with that joint kernel, so no second residual, family kernel,
     cut-set, or counting-rate definition is introduced.
   * English searches for finite cover/cut set/sufficiency/blind kernel,
     marginal capture/gain/diminishing, counting weight, and escape-rate
     antitonicity found `FiniteAnchorCoverage.coveredInputs` and
     `BudgetedEscapeRateAntitone.budgeted_escape_rate_bounds_and_antitone`.
     `coveredInputs` unions finite anchor suites of arbitrary inputs and has no
     target residual or definition kernel, so it does not state clause one.
     The budget theorem's second conjunct is exactly clause four at a general
     weight; it is applied directly here to the separately stated finite
     counting weight. Clause three instead keeps the source mass `nu` as a
     monotone parameter.
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
     `Set.mem_range_self`, `Set.ncard_le_ncard`, and `Set.mem_iUnion`; they
     carry finite extraction, actual-range recovery, and counting monotonicity.
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
open D5.S3.ConceptDynamics.DefinitionEscape.ResidualJoinLaw
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A finite dependent subfamily is sufficient when the target can be
recovered on the actual range of its joint readout with the baseline. -/
def finiteSelectionSufficientOnRange
    {I X C Target : Type*} {V : I → Type*}
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) : Prop :=
  ∃ (n : ℕ) (selected : Fin n → Gamma)
      (recover : Set.range
        (conceptJoin q (jointReadout
          (fun index => definitions (selected index).1))) → Target),
    ∀ x, target x = recover
      ⟨conceptJoin q (jointReadout
        (fun index => definitions (selected index).1)) x,
        Set.mem_range_self x⟩

/-- On a finite state space, all four finite-cover and mass/counting clauses
hold for a dependent family of definition codomains. A definition's cut is the
part of the canonical target defect outside its imported `conceptKernel`. The
second clause recovers only on the actual range of a finite joint readout. The
third is parameterized by an arbitrary monotone mass `nu`, while the fourth is
the separately stated finite-counting escape-rate law. -/
theorem finite_cover_counting
    {I X C Target Strategy Added : Type*} {V : I → Type*} [Finite X]
    (Gamma Delta : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) (d : I)
    (supplement : Strategy → Concept X Added) (cost : Strategy → Real)
    (nu : Set (X × X) → Real) (nu_monotone : Monotone nu)
    (budget1 budget2 : Real) :
    let countingWeight : EscapeWeight (X × X) :=
      { mass := fun set => (set.ncard : Real)
        empty_mass := by simp
        mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
    (defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ ↔
        (⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => definitions item.1)
              definition)ᶜ) =
          defectRelation q target) ∧
      (defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ →
        finiteSelectionSufficientOnRange Gamma definitions q target) ∧
      (Gamma ⊆ Delta ∧ d ∉ Delta →
        nu ((defectRelation q target ∩
              jointKernel (fun item : Delta => definitions item.1)) ∩
            ({pair : X × X |
              Setoid.ker (definitions d) pair.1 pair.2} : Set (X × X))ᶜ) ≤
          nu ((defectRelation q target ∩
              jointKernel (fun item : Gamma => definitions item.1)) ∩
            ({pair : X × X |
              Setoid.ker (definitions d) pair.1 pair.2} : Set (X × X))ᶜ)) ∧
      ((defectRelation q target).Nonempty →
        (∃ strategy, cost strategy ≤ budget1) →
        budget1 ≤ budget2 →
        budgetedEscapeRate q supplement target cost countingWeight budget2 ≤
          budgetedEscapeRate q supplement target cost countingWeight budget1) := by
  letI := Fintype.ofFinite X
  dsimp only
  have coverCriterion :
      defectRelation q target ∩
            jointKernel (fun item : Gamma => definitions item.1) = ∅ ↔
        (⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => definitions item.1)
              definition)ᶜ) =
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
            pair ∈ jointKernel (fun item : Gamma => definitions item.1) := by
          apply Set.mem_iInter.2
          intro definition
          by_contra pairNotInKernel
          apply pairNotCovered
          apply Set.mem_iUnion.2
          exact ⟨definition, pairInResidual, pairNotInKernel⟩
        have pairBlind : pair ∈
            defectRelation q target ∩
              jointKernel (fun item : Gamma => definitions item.1) :=
          ⟨pairInResidual, pairInJoint⟩
        rw [residualEmpty] at pairBlind
        exact pairBlind
    · intro coverEquality
      apply Set.eq_empty_iff_forall_notMem.2
      intro pair pairBlind
      have pairCovered :
          pair ∈ ⋃ definition : Gamma,
            defectRelation q target ∩
              (conceptKernel (fun item : Gamma => definitions item.1)
                definition)ᶜ := by
        rw [coverEquality]
        exact pairBlind.1
      rcases Set.mem_iUnion.1 pairCovered with ⟨definition, pairInCut⟩
      have pairInKernel :
          pair ∈ conceptKernel
            (fun item : Gamma => definitions item.1) definition :=
        Set.mem_iInter.1 pairBlind.2 definition
      exact pairInCut.2 pairInKernel
  refine ⟨coverCriterion, ?_, ?_, ?_⟩
  · intro residualEmpty
    have residualCover :
        defectRelation q target ⊆
          ⋃ definition : Gamma,
            defectRelation q target ∩
              (conceptKernel (fun item : Gamma => definitions item.1)
                definition)ᶜ := by
      rw [(coverCriterion.mp residualEmpty)]
    rcases Set.finite_subset_iUnion (Set.toFinite (defectRelation q target))
        residualCover with ⟨selectedSet, selectedFinite, selectedCover⟩
    letI : Fintype selectedSet := selectedFinite.fintype
    let n := Fintype.card selectedSet
    let selected : Fin n → Gamma :=
      fun index => ((Fintype.equivFin selectedSet).symm index).1
    have joinedDefectEmpty :
        defectRelation
            (conceptJoin q (jointReadout
              (fun index => definitions (selected index).1))) target = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro pair pairInJoinedDefect
      have pairInBaselineDefect : pair ∈ defectRelation q target :=
        ⟨congrArg Prod.fst pairInJoinedDefect.1, pairInJoinedDefect.2⟩
      have pairCovered := selectedCover pairInBaselineDefect
      rcases Set.mem_iUnion.1 pairCovered with ⟨definition, pairCovered⟩
      rcases Set.mem_iUnion.1 pairCovered with
        ⟨definitionInSelected, pairInCut⟩
      let selectedDefinition : selectedSet :=
        ⟨definition, definitionInSelected⟩
      let index : Fin n := Fintype.equivFin selectedSet selectedDefinition
      have definitionAtIndex : selected index = definition := by
        simp [selected, index, selectedDefinition, n]
      have selectedEqual :
          definitions (selected index).1 pair.1 =
            definitions (selected index).1 pair.2 := by
        exact congrFun (congrArg Prod.snd pairInJoinedDefect.1) index
      have pairInKernel :
          pair ∈ conceptKernel
            (fun item : Gamma => definitions item.1) definition := by
        change definitions definition.1 pair.1 = definitions definition.1 pair.2
        rw [← definitionAtIndex]
        exact selectedEqual
      exact pairInCut.2 pairInKernel
    let extended := conceptJoin q (jointReadout
      (fun index => definitions (selected index).1))
    let recover : Set.range extended → Target := fun observed =>
      target (Classical.choose observed.property)
    refine ⟨n, selected, recover, ?_⟩
    intro x
    change target x = target (Classical.choose (Set.mem_range_self x))
    by_contra targetDifferent
    have representativeEqual :
        extended (Classical.choose (Set.mem_range_self x)) = extended x :=
      Classical.choose_spec (Set.mem_range_self x)
    have pairInDefect :
        (Classical.choose (Set.mem_range_self x), x) ∈
          defectRelation extended target :=
      ⟨representativeEqual, Ne.symm targetDifferent⟩
    rw [joinedDefectEmpty] at pairInDefect
    exact pairInDefect
  · rintro ⟨gammaSubsetDelta, _dFresh⟩
    apply nu_monotone
    have capturedSubset :
        (defectRelation q target ∩
            jointKernel (fun item : Delta => definitions item.1)) ∩
            ({pair : X × X |
              Setoid.ker (definitions d) pair.1 pair.2} : Set (X × X))ᶜ ⊆
          (defectRelation q target ∩
            jointKernel (fun item : Gamma => definitions item.1)) ∩
            ({pair : X × X |
              Setoid.ker (definitions d) pair.1 pair.2} : Set (X × X))ᶜ := by
      rintro pair ⟨pairInDeltaResidual, pairSeparated⟩
      refine ⟨⟨pairInDeltaResidual.1, ?_⟩, pairSeparated⟩
      apply Set.mem_iInter.2
      intro definition
      let deltaDefinition : Delta :=
        ⟨definition.1, gammaSubsetDelta definition.2⟩
      have deltaEqual :=
        Set.mem_iInter.1 pairInDeltaResidual.2 deltaDefinition
      change definitions deltaDefinition.1 pair.1 =
        definitions deltaDefinition.1 pair.2 at deltaEqual
      change definitions definition.1 pair.1 = definitions definition.1 pair.2
      simpa only [deltaDefinition] using deltaEqual
    exact capturedSubset
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

/- The selected Boolean coordinate has codomain `Bool`, while the other
candidate has codomain `Unit`; this witnesses the genuinely dependent family
surface of the cover and finite-range clauses. -/
example :
    let V : Bool → Type := fun index => if index then Bool else Unit
    let definitions : ∀ index, Concept Bool (V index) := fun index => by
      cases index
      · exact fun _ => ()
      · exact id
    let Gamma : Set Bool := {true}
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    (defectRelation q target).Nonempty ∧
      defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ ∧
      finiteSelectionSufficientOnRange Gamma definitions q target := by
  dsimp only
  let V : Bool → Type := fun index => if index then Bool else Unit
  let definitions : ∀ index, Concept Bool (V index) := fun index => by
    cases index
    · exact fun _ => ()
    · exact id
  let Gamma : Set Bool := {true}
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  have baselineNonempty : (defectRelation q target).Nonempty :=
    ⟨(false, true), rfl, Bool.false_ne_true⟩
  have residualEmpty :
      defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro pair ⟨pairInDefect, pairInJoint⟩
    have pairInIdentityKernel := Set.mem_iInter.1 pairInJoint
      (⟨true, Set.mem_singleton_iff.mpr rfl⟩ : Gamma)
    have pairEqual : pair.1 = pair.2 := by
      simpa [conceptKernel, definitions, V] using pairInIdentityKernel
    exact pairInDefect.2 (congrArg target pairEqual)
  have package := finite_cover_counting Gamma Gamma definitions q target true
    (fun _ : Unit => (id : Concept Bool Bool)) (fun _ => 0)
    (fun set : Set (Bool × Bool) => (set.ncard : Real))
    (fun first second subset => by
      change (first.ncard : Real) ≤ (second.ncard : Real)
      exact_mod_cast Set.ncard_le_ncard subset) 0 1
  exact ⟨baselineNonempty, residualEmpty, package.2.1 residualEmpty⟩

/- On an empty state type the actual joint-readout range is empty, so range
recovery exists even with an empty target. Requiring recovery on the whole
ambient codomain is strictly stronger and is false in this instance. -/
example :
    let definitions : ∀ _ : Unit, Concept Empty Unit := fun _ => Empty.elim
    let Gamma : Set Unit := ∅
    let q : Concept Empty Unit := Empty.elim
    let target : Concept Empty Empty := Empty.elim
    finiteSelectionSufficientOnRange Gamma definitions q target ∧
      ¬finiteSelectionSufficient
        (∅ : Set (Concept Empty Unit)) q target := by
  dsimp only
  let definitions : ∀ _ : Unit, Concept Empty Unit := fun _ => Empty.elim
  let Gamma : Set Unit := ∅
  let q : Concept Empty Unit := Empty.elim
  let target : Concept Empty Empty := Empty.elim
  constructor
  · refine ⟨0, Fin.elim0, ?_, ?_⟩
    · intro observed
      exact Empty.elim (Classical.choose observed.property)
    · intro x
      exact x.elim
  · rintro ⟨n, selected, recover, _recovery⟩
    exact (recover ((), fun _ => ())).elim

/- With no definitions, the Boolean residual is neither covered nor recoverable
from any selected range. This rejects unconditional cover and sufficiency. -/
example :
    let definitions : ∀ _ : Unit, Concept Bool Unit := fun _ _ => ()
    let Gamma : Set Unit := ∅
    let q : Concept Bool Unit := fun _ => ()
    let target : Concept Bool Bool := id
    (defectRelation q target ∩
        jointKernel (fun item : Gamma => definitions item.1)).Nonempty ∧
      (⋃ definition : Gamma,
        defectRelation q target ∩
          (conceptKernel (fun item : Gamma => definitions item.1)
            definition)ᶜ) ≠ defectRelation q target ∧
      ¬finiteSelectionSufficientOnRange Gamma definitions q target := by
  dsimp only
  let definitions : ∀ _ : Unit, Concept Bool Unit := fun _ _ => ()
  let Gamma : Set Unit := ∅
  let q : Concept Bool Unit := fun _ => ()
  let target : Concept Bool Bool := id
  have residualNonempty :
      (defectRelation q target ∩
        jointKernel (fun item : Gamma => definitions item.1)).Nonempty :=
    ⟨(false, true), by
      simp [defectRelation, jointKernel, conceptKernel, target]⟩
  refine ⟨residualNonempty, ?_, ?_⟩
  · intro coverEquality
    have pairCovered : (false, true) ∈
        ⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => definitions item.1)
              definition)ᶜ := by
      rw [coverEquality]
      exact ⟨rfl, Bool.false_ne_true⟩
    simp at pairCovered
  · rintro ⟨n, selected, recover, recovery⟩
    have extensionEqual :
        conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)) false =
          conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)) true := by
      apply Prod.ext rfl
      funext index
      exact False.elim (selected index).2
    have rangePointEqual :
        (⟨conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)) false,
            Set.mem_range_self false⟩ :
          Set.range (conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)))) =
        ⟨conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)) true,
          Set.mem_range_self true⟩ := Subtype.ext extensionEqual
    have falseEqualsTrue := (recovery false).trans
      ((congrArg recover rangePointEqual).trans (recovery true).symm)
    exact Bool.false_ne_true falseEqualsTrue

/- A non-counting monotone weight gives one ordered Boolean residual pair mass
three. Negation removes that pair before the fresh identity candidate arrives,
so weighted marginal capture strictly decreases and the reverse inequality is
false. -/
example :
    let definitions : ∀ _ : Bool, Concept Bool Bool :=
      fun index => if index then id else fun value => !value
    let Gamma : Set Bool := ∅
    let Delta : Set Bool := {false}
    let nu : Set (Bool × Bool) → Real := fun set =>
      3 * ((set ∩ {(false, true)}).ncard : Real)
    Gamma ⊆ Delta ∧ true ∉ Delta ∧ Monotone nu ∧
      nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Delta => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) <
        nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Gamma => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) ∧
      ¬nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Gamma => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) ≤
        nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Delta => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) := by
  dsimp only
  let definitions : ∀ _ : Bool, Concept Bool Bool :=
    fun index => if index then id else fun value => !value
  let Gamma : Set Bool := ∅
  let Delta : Set Bool := {false}
  let nu : Set (Bool × Bool) → Real := fun set =>
    3 * ((set ∩ {(false, true)}).ncard : Real)
  have nuMonotone : Monotone nu := by
    intro first second subset
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact_mod_cast Set.ncard_le_ncard (by
      rintro pair ⟨pairInFirst, pairInSingleton⟩
      exact ⟨subset pairInFirst, pairInSingleton⟩)
  have largerZero :
      nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Delta => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) = 0 := by
    simp [nu, Delta, definitions, jointKernel, conceptKernel, defectRelation]
  have smallerThree :
      nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Gamma => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) = 3 := by
    simp [nu, Gamma, definitions, jointKernel, conceptKernel, defectRelation]
  have strictDecrease :
      nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Delta => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) <
        nu ((defectRelation (fun _ : Bool => ()) (id : Concept Bool Bool) ∩
            jointKernel (fun item : Gamma => definitions item.1)) ∩
          ({pair : Bool × Bool |
            Setoid.ker (definitions true) pair.1 pair.2} : Set (Bool × Bool))ᶜ) := by
    rw [largerZero, smallerThree]
    norm_num
  exact ⟨Set.empty_subset _, by simp, nuMonotone, strictDecrease,
    not_le_of_gt strictDecrease⟩

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
