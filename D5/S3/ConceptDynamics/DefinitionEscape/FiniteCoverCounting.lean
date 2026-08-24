/- GID: D5/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/FiniteCoverCounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two finite-cover clauses and counting antitonicity hold; the weak
   EscapeWeight interface does not imply marginal capture. -/

import D5.S3.AnalyticClosure.Budget.BudgetedEscapeRateAntitone
import D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
import D5.S3.ConceptDynamics.Refinement.InductiveSufficiency
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Lattice

/- Scope of this module: `finite_cover_counting` packages the two cover clauses
and the counting clause proved below. The marginal clause is retained as a
proposition over the CAS definitions

  M(S) = nu.mass (defectRelation (conceptJoin q (jointReadout S)) target),
  F(S) = M(empty) - M(S).

`EscapeWeight` has no additivity or submodularity law from which its diminishing
return could be proved. A concrete `EscapeWeight` below refutes the proposition
at that weak interface; this does not refute the CAS measure semantics. The
counting clause uses finite subsets of Gamma, summed nonnegative candidate
costs, and the empty selection at a nonnegative budget, so it is provable. -/

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
     The budget theorem ranges over an arbitrary `Strategy`. The faithful CAS
     strategy below is `Finset Gamma`, with summed cost and a canonical empty
     selection. At a nonnegative smaller budget that selection supplies the
     theorem's nonempty feasible-value premise. The marginal formula remains
     outside the package: rewriting the CAS difference `M(empty) - M(S)` as a
     weighted union of cuts needs a mass additivity law absent from
     `EscapeWeight`.
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
   * Pinned Mathlib searches found exact lemmas `Set.finite_subset_iUnion` and
     `Set.mem_iUnion`; they carry finite extraction and the cover membership
     steps. Canonical realized-image recovery is reused through the repository
     theorem `inductive_sufficiency_criterion`.
   * A Loogle query for `Set.finite_subset_iUnion` returned that exact
     pinned-Mathlib declaration. The attempted
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
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Refinement.InductiveSufficiency
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- A finite dependent subfamily is sufficient when the target refines the
canonical realized-image factorization of its joint readout with the baseline. -/
def finiteSelectionSufficientOnRange
    {I X C Target : Type*} {V : I → Type*}
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) : Prop :=
  ∃ (n : ℕ) (selected : Fin n → Gamma),
    Refines target (Set.rangeFactorization
      (conceptJoin q (jointReadout
        (fun index => definitions (selected index).1))))

/-- The two source-valid cover clauses. The cut-cover equivalence is general;
only finite-subfamily extraction assumes `Finite X`, inside its own premise. -/
theorem finite_cover_laws
    {I X C Target : Type*} {V : I → Type*}
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) :
    (defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ ↔
        (⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => definitions item.1)
              definition)ᶜ) =
          defectRelation q target) ∧
      (Finite X ∧ defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ →
        finiteSelectionSufficientOnRange Gamma definitions q target) := by
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
  refine ⟨coverCriterion, ?_⟩
  · rintro ⟨finiteX, residualEmpty⟩
    letI : Finite X := finiteX
    letI := Fintype.ofFinite X
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
    have factors : Function.FactorsThrough target extended := by
      intro x y sameReadout
      by_contra targetDifferent
      have pairInDefect : (x, y) ∈ defectRelation extended target :=
        ⟨sameReadout, targetDifferent⟩
      rw [joinedDefectEmpty] at pairInDefect
      exact pairInDefect
    exact ⟨n, selected,
      (inductive_sufficiency_criterion extended target).1.mp factors⟩

/-- CAS residual mass `M(S) = nu(E(q join S; T))`. -/
def residualEscapeMass
    {I X C Target : Type*} {V : I → Type*}
    (S : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (nu : EscapeWeight (X × X)) : Real :=
  nu.mass (defectRelation
    (conceptJoin q (jointReadout (fun item : S => definitions item.1))) target)

/-- CAS total capture `F(S) = M(empty) - M(S)`. No weighted-cover equality is
built into this definition. -/
def capturedEscapeMass
    {I X C Target : Type*} {V : I → Type*}
    (S : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (nu : EscapeWeight (X × X)) : Real :=
  residualEscapeMass (∅ : Set I) definitions q target nu -
    residualEscapeMass S definitions q target nu

/-- The diminishing-marginal-capture formula over the CAS two-step definition
of `F`. This is a proposition, not a theorem: `EscapeWeight` supplies no
additivity or submodularity law from which to prove it. -/
def marginalCaptureLaw
    {I X C Target : Type*} {V : I → Type*}
    (Gamma Delta : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target) (d : I)
    (nu : EscapeWeight (X × X)) : Prop :=
  Gamma ⊆ Delta ∧ d ∉ Delta →
    capturedEscapeMass (Gamma ∪ {d}) definitions q target nu -
        capturedEscapeMass Gamma definitions q target nu ≥
      capturedEscapeMass (Delta ∪ {d}) definitions q target nu -
        capturedEscapeMass Delta definitions q target nu

/-- A finite CAS selection reveals exactly the coordinates in the selected
subset. Unselected coordinates carry `none` and add no distinction. -/
def finiteSelectionSupplement
    {I X : Type*} {V : I → Type*} [DecidableEq I]
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i)) :
    Finset Gamma → Concept X (∀ item : Gamma, Option (V item.1)) :=
  fun selection state item =>
    if item ∈ selection then some (definitions item.1 state) else none

/-- CAS selection cost `C(S) = sum d in S, c(d)`. -/
def finiteSelectionCost
    {I : Type*} [DecidableEq I]
    (Gamma : Set I) (candidateCost : I → Real) (selection : Finset Gamma) : Real :=
  ∑ item ∈ selection, candidateCost item.1

/-- The CAS counting escape-rate direction on finite subsets of `Gamma`.
Nonnegative candidate costs and a nonnegative smaller budget make the empty
selection feasible. -/
def countingEscapeAntitoneLaw
    {I X C Target : Type*} {V : I → Type*} [Finite X] [DecidableEq I]
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I → Real) (budget1 budget2 : Real) : Prop :=
  let countingWeight : EscapeWeight (X × X) :=
    { mass := fun set => (set.ncard : Real)
      empty_mass := by simp
      mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
  (∀ definition ∈ Gamma, 0 ≤ candidateCost definition) ∧
      0 ≤ budget1 ∧ budget1 ≤ budget2 ∧
      0 < countingWeight.mass (defectRelation q target) →
    budgetedEscapeRate q
        (finiteSelectionSupplement Gamma definitions) target
        (finiteSelectionCost Gamma candidateCost) countingWeight budget2 ≤
      budgetedEscapeRate q
        (finiteSelectionSupplement Gamma definitions) target
        (finiteSelectionCost Gamma candidateCost) countingWeight budget1

/-- The CAS counting escape rate is antitone in the budget. The empty finite
selection witnesses feasibility at the smaller nonnegative budget. -/
theorem counting_escape_antitone_law
    {I X C Target : Type*} {V : I → Type*} [Finite X] [DecidableEq I]
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I → Real) (budget1 budget2 : Real) :
    countingEscapeAntitoneLaw Gamma definitions q target candidateCost
      budget1 budget2 := by
  let countingWeight : EscapeWeight (X × X) :=
    { mass := fun set => (set.ncard : Real)
      empty_mass := by simp
      mass_nonnegative := fun set => Nat.cast_nonneg set.ncard }
  change
    ((∀ definition ∈ Gamma, 0 ≤ candidateCost definition) ∧
        0 ≤ budget1 ∧ budget1 ≤ budget2 ∧
        0 < countingWeight.mass (defectRelation q target)) →
      budgetedEscapeRate q
          (finiteSelectionSupplement Gamma definitions) target
          (finiteSelectionCost Gamma candidateCost) countingWeight budget2 ≤
        budgetedEscapeRate q
          (finiteSelectionSupplement Gamma definitions) target
          (finiteSelectionCost Gamma candidateCost) countingWeight budget1
  rintro ⟨_candidateCostsNonnegative, budgetOneNonnegative, budgetOrder,
    baselineMassPositive⟩
  have escapeAtMostTotal (selection : Finset Gamma) :
      countingWeight.mass
          (defectRelation
            (conceptJoin q
              (finiteSelectionSupplement Gamma definitions selection)) target) ≤
        countingWeight.mass (defectRelation q target) := by
    change
      ((defectRelation
        (conceptJoin q
          (finiteSelectionSupplement Gamma definitions selection)) target).ncard :
          Real) ≤ (defectRelation q target).ncard
    exact_mod_cast Set.ncard_le_ncard (by
      rintro pair pairInDefect
      exact ⟨congrArg Prod.fst pairInDefect.1, pairInDefect.2⟩)
  have valuesNonempty :
      (budgetedEscapeValues q
        (finiteSelectionSupplement Gamma definitions) target
        (finiteSelectionCost Gamma candidateCost) countingWeight budget1).Nonempty := by
    let selection : Finset Gamma := ∅
    refine ⟨countingWeight.mass
        (defectRelation
          (conceptJoin q
            (finiteSelectionSupplement Gamma definitions selection)) target) /
          countingWeight.mass (defectRelation q target),
      selection, ?_, rfl⟩
    change finiteSelectionCost Gamma candidateCost selection ≤ budget1
    simpa [finiteSelectionCost, selection] using budgetOneNonnegative
  exact (budgeted_escape_rate_bounds_and_antitone q
    (finiteSelectionSupplement Gamma definitions) target
    (finiteSelectionCost Gamma candidateCost) countingWeight
    baselineMassPositive escapeAtMostTotal valuesNonempty).2 budgetOrder

/-- The two cover laws and the counting escape-rate law, packaged together. -/
theorem finite_cover_counting
    {I X C Target : Type*} {V : I → Type*} [Finite X] [DecidableEq I]
    (Gamma : Set I) (definitions : ∀ i, Concept X (V i))
    (q : Concept X C) (target : Concept X Target)
    (candidateCost : I → Real) (budget1 budget2 : Real) :
    (defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ ↔
        (⋃ definition : Gamma,
          defectRelation q target ∩
            (conceptKernel (fun item : Gamma => definitions item.1)
              definition)ᶜ) =
          defectRelation q target) ∧
      (Finite X ∧ defectRelation q target ∩
          jointKernel (fun item : Gamma => definitions item.1) = ∅ →
        finiteSelectionSufficientOnRange Gamma definitions q target) ∧
      countingEscapeAntitoneLaw Gamma definitions q target candidateCost
        budget1 budget2 := by
  have coverPackage := finite_cover_laws Gamma definitions q target
  exact ⟨coverPackage.1, coverPackage.2,
    counting_escape_antitone_law Gamma definitions q target candidateCost
      budget1 budget2⟩

/- This counterexample lives inside the current CAS Lean interface: its weight
has zero empty mass and nonnegative mass, exactly as `EscapeWeight` requires.
It shows that those two laws do not imply marginal submodularity. The source's
measure/additive-weight reading is stronger and is not refuted here. -/
theorem marginal_capture_law_not_implied_by_escape_weight :
    ∃ nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)),
      ¬marginalCaptureLaw (∅ : Set Bool) {false}
        (fun index => if index then Prod.snd else Prod.fst)
        (fun _ : Bool × Bool => ()) id true nu := by
  let firstPair : (Bool × Bool) × (Bool × Bool) :=
    ((false, false), (true, false))
  let secondPair : (Bool × Bool) × (Bool × Bool) :=
    ((false, false), (false, true))
  let nu : EscapeWeight ((Bool × Bool) × (Bool × Bool)) :=
    { mass := fun set =>
        @ite Real (secondPair ∈ set ∧ firstPair ∉ set)
          (Classical.propDecidable _) 1 0
      empty_mass := by simp
      mass_nonnegative := by intro set; split_ifs <;> norm_num }
  refine ⟨nu, ?_⟩
  intro law
  have inequality := law ⟨Set.empty_subset _, by simp⟩
  have emptyResidualMass :
      residualEscapeMass (∅ : Set Bool)
        (fun index => if index then Prod.snd else Prod.fst)
        (fun _ : Bool × Bool => ()) id nu = 0 := by
    simp [residualEscapeMass, nu, firstPair, secondPair, defectRelation,
      conceptJoin]
    intro _secondEqual
    funext item
    exact False.elim item.2
  have freshResidualMass :
      residualEscapeMass ({true} : Set Bool)
        (fun index => if index then Prod.snd else Prod.fst)
        (fun _ : Bool × Bool => ()) id nu = 0 := by
    simp [residualEscapeMass, nu, firstPair, secondPair, defectRelation,
      conceptJoin]
    intro _secondEqual
    funext item
    have itemTrue : item.1 = true := Set.mem_singleton_iff.mp item.2
    simp [jointReadout, itemTrue]
  have combinedResidualMass :
      residualEscapeMass (({false} : Set Bool) ∪ {true})
        (fun index => if index then Prod.snd else Prod.fst)
        (fun _ : Bool × Bool => ()) id nu = 0 := by
    simp [residualEscapeMass, nu, firstPair, secondPair, defectRelation,
      conceptJoin]
    intro secondEqual
    let item : { index : Bool //
        index ∈ (({false} : Set Bool) ∪ {true}) } := ⟨true, by simp⟩
    have sameAtItem := congrFun secondEqual item
    simp [jointReadout, item] at sameAtItem
  have deltaSecondEqual :
      jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then Prod.snd else Prod.fst) (false, false) =
        jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then Prod.snd else Prod.fst) (false, true) := by
    funext item
    have itemFalse : item.1 = false := Set.mem_singleton_iff.mp item.2
    simp [jointReadout, itemFalse]
  have deltaFirstDifferent :
      jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then Prod.snd else Prod.fst) (false, false) ≠
        jointReadout
          (fun item : ({false} : Set Bool) =>
            if item.1 then Prod.snd else Prod.fst) (true, false) := by
    intro sameReadout
    let item : ({false} : Set Bool) := ⟨false, by simp⟩
    have sameAtItem := congrFun sameReadout item
    simp [jointReadout, item] at sameAtItem
  have deltaResidualMass :
      residualEscapeMass ({false} : Set Bool)
        (fun index => if index then Prod.snd else Prod.fst)
        (fun _ : Bool × Bool => ()) id nu = 1 := by
    simp [residualEscapeMass, nu, firstPair, secondPair, defectRelation,
      conceptJoin]
    exact ⟨deltaSecondEqual, deltaFirstDifferent⟩
  simp only [Set.empty_union, capturedEscapeMass, emptyResidualMass,
    freshResidualMass, combinedResidualMass, deltaResidualMass] at inequality
  norm_num at inequality

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
  have package := finite_cover_laws Gamma definitions q target
  exact ⟨baselineNonempty, residualEmpty,
    package.2 ⟨inferInstance, residualEmpty⟩⟩

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
  · refine ⟨0, Fin.elim0, ?_⟩
    apply (inductive_sufficiency_criterion _ _).1.mp
    intro x
    exact x.elim
  · rintro ⟨n, selected, refinement⟩
    rcases refinement with ⟨recover, _factorization⟩
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
  · rintro ⟨n, selected, refinement⟩
    have extensionEqual :
        conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)) false =
          conceptJoin q (jointReadout
            (fun index => definitions (selected index).1)) true := by
      apply Prod.ext rfl
      funext index
      exact False.elim (selected index).2
    have factors := (inductive_sufficiency_criterion
      (conceptJoin q (jointReadout
        (fun index => definitions (selected index).1))) target).1.mpr refinement
    exact Bool.false_ne_true (factors extensionEqual)

#print axioms finite_cover_counting
#print axioms counting_escape_antitone_law
#print axioms marginal_capture_law_not_implied_by_escape_weight

end D5.S3.ConceptDynamics.DefinitionEscape.FiniteCoverCounting
