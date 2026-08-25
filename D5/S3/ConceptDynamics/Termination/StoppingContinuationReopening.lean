/- GID: D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Termination/StoppingContinuationReopening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed stages can close while changing targets repeatedly create new defects. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Tactic

/- Library-search audit trail (2026-08-25):
   * Shape search `rg -n 'Set \(X × X\)|defectRelation|target.*defect|
     residual|escape|残差|逃逸' D5/S3/ConceptDynamics -g '*.lean'` found the
     canonical `defectRelation` and the domain-restriction pattern in
     `Transport/OverreachWithoutLicense`. Reopening below intersects that
     existing relation with the old and new domain squares; it introduces no
     second escape-residual definition.
   * Metric-shape and bilingual synonym search `rg -n 'worst.*fiber|fiber.*diam|
     diameter|ediam|sSup.*dist|supremum.*distance|approximate.*closed|tolerance|
     deviation|最坏|纤维|直径|上确界|近似闭合|容差' D5 .lake/packages/mathlib/Mathlib
     -g '*.lean'` found no DECT worst-fiber declaration. It found the exact
     pinned primitive `Metric.ediam`, including `ediam_empty`,
     `ediam_singleton`, and `ediam_le_iff`; `worstFiberDefect` reuses it.
   * Persistent-change search `rg -n 'OpenWorld|open.world|persistent.*change|
     Frequently.*atTop|frequently_atTop|stagewise|parameter.*change|开放世界|
     持续变化|参数.*变化'` over ConceptDynamics and Mathlib found no repository
     open-world predicate and found `Filter.frequently_atTop`, reused for the
     infinite-reopening and quantifier-separation controls.
   * Stopping synonym search `rg -n 'BudgetStop|budget.*stop|gain.*cost|
     sSup.*threshold|NoProposal|MethodStopped|预算停止|方法停止|停止条件'
     D5/S3/ConceptDynamics -g '*.lean'` found no exact stop predicate. The
     neighboring finite-cover modules define residual mass and candidate cost,
     not the section-43 supremum or method-value equations.
   * Neighbor vocabulary `ls D5/S3/ConceptDynamics/Termination` and
     `git grep -n '^def \|^  def ' -- D5/S3/ConceptDynamics | head -80` found no
     reusable local-completion, persistent-field, or genuine-reopening
     definition. Source search for `操作族|operationFamily|NoProposal|E_S` found
     no rule connecting operation family to closure and no signature for the
     method symbol beyond the displayed equation in section 43.
   * Pinned Mathlib supplies `csSup_le_iff` for the conditional equivalence
     between the source's real `sSup` formula and its pointwise consequence.
     `Real.sSup_empty` fixes the empty feasible case at zero; the source formula
     remains the definition even when the set is empty or unbounded. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Termination.StoppingContinuationReopening

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff

/-- Target closure means exactly that the canonical target defect is empty. -/
def Closed {X Coordinate Target : Type*}
    (readout : Concept X Coordinate) (target : Concept X Target) : Prop :=
  defectRelation readout target = ∅

/-- The section-9.1 quantity `Delta(q;T)`: the supremum of target diameters over
all readout fibers. `Metric.ediam` makes an empty fiber contribute zero and an
unbounded family of distances contribute `top`, without extra hypotheses. -/
noncomputable def worstFiberDefect
    {X Coordinate Target : Type*} [MetricSpace Target]
    (readout : Concept X Coordinate) (target : Concept X Target) : ENNReal :=
  ⨆ coordinate,
    Metric.ediam (target '' {object | readout object = coordinate})

/-- Approximate closure uses the canonical worst fiber defect from section 9.1. -/
def ApproximatelyClosed
    {X Coordinate Target : Type*} [MetricSpace Target]
    (readout : Concept X Coordinate) (target : Concept X Target)
    (precision : ENNReal) : Prop :=
  worstFiberDefect readout target ≤ precision

/-- The source's budget-stop formula. The real supremum is intentionally total:
`sSup ∅ = 0`, while the conditional pointwise characterization is separate. -/
noncomputable def BudgetStop {Decision : Type*}
    (cost gain : Decision -> Real) (budget threshold : Real) : Prop :=
  sSup ((fun decision => gain decision / cost decision) ''
    {decision | cost decision ≤ budget}) ≤ threshold

/-- Method stopping is the literal distinguished-value equation in section 43. -/
def MethodStopped {System Evidence Proposal : Type*}
    (method : System -> Evidence -> Proposal)
    (system : System) (evidence : Evidence) (noProposal : Proposal) : Prop :=
  method system evidence = noProposal

/-- The parameter record named by local completion and reopening. Precision is
an extended nonnegative metric bound so empty and unbounded suprema stay total. -/
structure LocalParameters (World Target Operation : Type*) where
  objectDomain : Set World
  target : Concept World Target
  operationFamily : Set Operation
  precision : ENNReal

/-- Local completion checks approximate target closure on the supplied object
domain at the supplied precision. Section 43 gives no operation-family action on
closure, so that field is carried by the parameter record but is not invented
as an additional premise. -/
def LocallyComplete
    {World Coordinate Target Operation : Type*} [MetricSpace Target]
    (parameters : LocalParameters World Target Operation)
    (readout : Concept World Coordinate) : Prop :=
  ApproximatelyClosed
    (fun object : ↑parameters.objectDomain => readout object.1)
    (fun object : ↑parameters.objectDomain => parameters.target object.1)
    parameters.precision

/-- At least one member of the local-completion parameter quadruple changes. -/
def LocalParametersChanged
    {World Target Operation : Type*}
    (current next : LocalParameters World Target Operation) : Prop :=
  current.objectDomain ≠ next.objectDomain ∨
    current.target ≠ next.target ∨
    current.precision ≠ next.precision ∨
    current.operationFamily ≠ next.operationFamily

/-- One fixed field changes at every adjacent stage. This is the
`exists field, forall stage` reading of "at least one keeps changing". -/
def OpenWorldSequence
    {World Target Operation : Type*}
    (parameters : Nat -> LocalParameters World Target Operation) : Prop :=
  (∀ stage,
      (parameters stage).objectDomain ≠
        (parameters (stage + 1)).objectDomain) ∨
    (∀ stage,
      (parameters stage).target ≠ (parameters (stage + 1)).target) ∨
    (∀ stage,
      (parameters stage).precision ≠ (parameters (stage + 1)).precision) ∨
    (∀ stage,
      (parameters stage).operationFamily ≠
        (parameters (stage + 1)).operationFamily)

/-- Reopening requires an allowed parameter change and a genuinely new
canonical target defect: a pair present after the change but absent before it.
Both defect sets are expressed in the ambient world so domain changes compare. -/
def Reopens
    {World Coordinate Target Operation Definition : Type*}
    (current next : LocalParameters World Target Operation)
    (currentLanguage nextLanguage : Set Definition)
    (readout : Concept World Coordinate) : Prop :=
  (LocalParametersChanged current next ∨
      currentLanguage ≠ nextLanguage) ∧
    (((defectRelation readout next.target) ∩
          (next.objectDomain ×ˢ next.objectDomain)) \
      ((defectRelation readout current.target) ∩
          (current.objectDomain ×ˢ current.objectDomain))).Nonempty

/-- On a nonempty feasible set with bounded-above real ratios, the source's
supremum stop formula is equivalent to the useful pointwise form. -/
theorem budget_stop_iff_pointwise
    {Decision : Type*} (cost gain : Decision -> Real)
    (budget threshold : Real)
    (feasibleNonempty : ({decision | cost decision ≤ budget} : Set Decision).Nonempty)
    (ratiosBounded : BddAbove
      ((fun decision => gain decision / cost decision) ''
        {decision | cost decision ≤ budget})) :
    BudgetStop cost gain budget threshold ↔
      ∀ decision, cost decision ≤ budget ->
        gain decision / cost decision ≤ threshold := by
  rw [BudgetStop, csSup_le_iff ratiosBounded (feasibleNonempty.image _)]
  constructor
  · intro everyRatio decision feasible
    exact everyRatio _ ⟨decision, feasible, rfl⟩
  · intro stopped ratio ratioInImage
    rcases ratioInImage with ⟨decision, feasible, rfl⟩
    exact stopped decision feasible

/-- There is a persistent-target open-world sequence that closes after every
fixed-stage repair and is reopened by the next target at every transition. -/
theorem stagewise_completion_with_infinite_reopening :
    ∃ (parameters : Nat -> LocalParameters Nat Real Unit)
      (languages : Nat -> Set Unit)
      (systems : Nat -> Concept Nat Real),
      (∀ stage, (parameters stage).objectDomain.Nonempty) ∧
        OpenWorldSequence parameters ∧
        (∀ stage, LocallyComplete (parameters stage) (systems stage)) ∧
        (∃ᶠ stage in Filter.atTop,
          Reopens (parameters stage) (parameters (stage + 1))
            (languages stage) (languages (stage + 1)) (systems stage)) := by
  let targetAt : Nat -> Concept Nat Real :=
    fun stage object => if object = stage then 1 else 0
  let parameters : Nat -> LocalParameters Nat Real Unit := fun stage =>
    { objectDomain := Set.univ
      target := targetAt stage
      operationFamily := Set.univ
      precision := 0 }
  let languages : Nat -> Set Unit := fun _ => ∅
  let systems : Nat -> Concept Nat Real := targetAt
  have targetChanges (stage : Nat) :
      (parameters stage).target ≠ (parameters (stage + 1)).target := by
    intro equalTargets
    have equalAtCurrent := congrFun equalTargets stage
    simp [parameters, targetAt] at equalAtCurrent
  have completeEveryStage (stage : Nat) :
      LocallyComplete (parameters stage) (systems stage) := by
    unfold LocallyComplete ApproximatelyClosed worstFiberDefect
    simp only [parameters]
    refine iSup_le fun coordinate => Metric.ediam_image_le_iff.2 ?_
    intro first firstInFiber second secondInFiber
    simp only [Set.mem_setOf_eq] at firstInFiber secondInFiber
    have targetsEqual :
        targetAt stage first.1 = targetAt stage second.1 :=
      firstInFiber.trans secondInFiber.symm
    simp [targetsEqual]
  have reopensEveryStage (stage : Nat) :
      Reopens (parameters stage) (parameters (stage + 1))
        (languages stage) (languages (stage + 1)) (systems stage) := by
    constructor
    · exact Or.inl (Or.inr (Or.inl (targetChanges stage)))
    · refine ⟨(stage + 1, stage + 2), ?_⟩
      simp [parameters, systems, targetAt, defectRelation]
  refine ⟨parameters, languages, systems, ?_, ?_, completeEveryStage, ?_⟩
  · intro stage
    simp [parameters]
  · exact Or.inr (Or.inl targetChanges)
  · refine Filter.frequently_atTop.2 ?_
    intro lowerBound
    exact ⟨lowerBound, le_rfl, reopensEveryStage lowerBound⟩

/-- The eight source assertions in one public package. The conditional pointwise
budget lemma above is useful, but is not part of the source package. -/
theorem stopping_continuation_reopening :
    (∀ {X Coordinate Target : Type*}
      (readout : Concept X Coordinate) (target : Concept X Target),
      Closed readout target ↔ defectRelation readout target = ∅) ∧
    (∀ {X Coordinate Target : Type*} [MetricSpace Target]
      (readout : Concept X Coordinate) (target : Concept X Target)
      (precision : ENNReal),
      ApproximatelyClosed readout target precision ↔
        worstFiberDefect readout target ≤ precision) ∧
    (∀ {Decision : Type*} (cost gain : Decision -> Real)
      (budget threshold : Real),
      BudgetStop cost gain budget threshold ↔
        sSup ((fun decision => gain decision / cost decision) ''
          {decision | cost decision ≤ budget}) ≤ threshold) ∧
    (∀ {System Evidence Proposal : Type*}
      (method : System -> Evidence -> Proposal)
      (system : System) (evidence : Evidence) (noProposal : Proposal),
      MethodStopped method system evidence noProposal ↔
        method system evidence = noProposal) ∧
    (∀ {World Coordinate Target Operation : Type*} [MetricSpace Target]
      (parameters : LocalParameters World Target Operation)
      (readout : Concept World Coordinate),
      LocallyComplete parameters readout ↔
        ApproximatelyClosed
          (fun object : ↑parameters.objectDomain => readout object.1)
          (fun object : ↑parameters.objectDomain => parameters.target object.1)
          parameters.precision) ∧
    (∀ {World Target Operation : Type*}
      (parameters : Nat -> LocalParameters World Target Operation),
      OpenWorldSequence parameters ↔
        ((∀ stage,
            (parameters stage).objectDomain ≠
              (parameters (stage + 1)).objectDomain) ∨
          (∀ stage,
            (parameters stage).target ≠ (parameters (stage + 1)).target) ∨
          (∀ stage,
            (parameters stage).precision ≠
              (parameters (stage + 1)).precision) ∨
          (∀ stage,
            (parameters stage).operationFamily ≠
              (parameters (stage + 1)).operationFamily))) ∧
    (∀ {World Coordinate Target Operation Definition : Type*}
      (current next : LocalParameters World Target Operation)
      (currentLanguage nextLanguage : Set Definition)
      (readout : Concept World Coordinate),
      Reopens current next currentLanguage nextLanguage readout ↔
        (LocalParametersChanged current next ∨
            currentLanguage ≠ nextLanguage) ∧
          (((defectRelation readout next.target) ∩
                (next.objectDomain ×ˢ next.objectDomain)) \
            ((defectRelation readout current.target) ∩
                (current.objectDomain ×ˢ current.objectDomain))).Nonempty) ∧
    (∃ (parameters : Nat -> LocalParameters Nat Real Unit)
      (languages : Nat -> Set Unit)
      (systems : Nat -> Concept Nat Real),
      (∀ stage, (parameters stage).objectDomain.Nonempty) ∧
        OpenWorldSequence parameters ∧
        (∀ stage, LocallyComplete (parameters stage) (systems stage)) ∧
        (∃ᶠ stage in Filter.atTop,
          Reopens (parameters stage) (parameters (stage + 1))
            (languages stage) (languages (stage + 1)) (systems stage))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl
  · exact stagewise_completion_with_infinite_reopening

/-- Negative control for conjunct 1: a constant readout hides a Boolean target. -/
theorem hidden_bool_target_is_not_closed :
    ¬Closed (fun _ : Bool => ()) (id : Concept Bool Bool) := by
  intro closed
  have hiddenPair :
      (false, true) ∈ defectRelation (fun _ : Bool => ())
        (id : Concept Bool Bool) :=
    ⟨rfl, Bool.false_ne_true⟩
  rw [closed] at hiddenPair
  exact hiddenPair

/-- Negative control for conjunct 2: a finite fiber with target distance one is
not approximately closed at precision zero. -/
theorem positive_fiber_diameter_is_not_approximately_closed :
    ¬ApproximatelyClosed (fun _ : Bool => ())
      (fun value : Bool => if value then (1 : Real) else 0) 0 := by
  intro approximatelyClosed
  have oneLeFiber : (1 : ENNReal) ≤
      Metric.ediam
        ((fun value : Bool => if value then (1 : Real) else 0) ''
          {value | (fun _ : Bool => ()) value = ()}) := by
    calc
      (1 : ENNReal) = edist (0 : Real) 1 := by norm_num
      _ ≤ Metric.ediam
          ((fun value : Bool => if value then (1 : Real) else 0) ''
            {value | (fun _ : Bool => ()) value = ()}) :=
        Metric.edist_le_ediam_of_mem
          ⟨false, by simp⟩ ⟨true, by simp⟩
  have oneLeWorst : (1 : ENNReal) ≤
      worstFiberDefect (fun _ : Bool => ())
        (fun value : Bool => if value then (1 : Real) else 0) :=
    oneLeFiber.trans (le_iSup
      (fun coordinate : Unit =>
        Metric.ediam
          ((fun value : Bool => if value then (1 : Real) else 0) ''
            {value | (fun _ : Bool => ()) value = coordinate})) ())
  have : (1 : ENNReal) ≤ 0 := oneLeWorst.trans approximatelyClosed
  norm_num at this

/-- Negative control for conjunct 3: a feasible ratio two exceeds threshold one. -/
theorem profitable_feasible_decision_is_not_budget_stopped :
    ¬BudgetStop (fun _ : Unit => (1 : Real)) (fun _ => 2) 1 1 := by
  norm_num [BudgetStop]

/-- Negative control for conjunct 4: without feasible nonemptiness, the
pointwise condition is vacuous while the source's `sSup ∅ = 0` formula is false
at a negative threshold. -/
theorem empty_feasible_set_separates_supremum_and_pointwise :
    ¬(BudgetStop (fun _ : Unit => (1 : Real)) (fun _ => 0) 0 (-1) ↔
      ∀ _decision : Unit, (1 : Real) ≤ 0 -> (0 : Real) / 1 ≤ -1) := by
  norm_num [BudgetStop]

/-- Negative control for conjunct 5: returning a proposal is not method stop. -/
theorem proposal_return_is_not_method_stopped :
    ¬MethodStopped (fun _ : Unit => id) () true false := by
  simp [MethodStopped]

/-- Negative control for conjunct 6: local completion reads the supplied zero
precision and rejects a nonconstant target on one readout fiber. -/
theorem zero_precision_nonconstant_fiber_is_not_locally_complete :
    let parameters : LocalParameters Bool Real Unit :=
      { objectDomain := Set.univ
        target := fun value => if value then 1 else 0
        operationFamily := Set.univ
        precision := 0 }
    ¬LocallyComplete parameters (fun _ => ()) := by
  dsimp
  intro locallyComplete
  have oneLeFiber : (1 : ENNReal) ≤
      Metric.ediam
        ((fun value : ↑(Set.univ : Set Bool) =>
            if value.1 then (1 : Real) else 0) ''
          {value | (fun _ : ↑(Set.univ : Set Bool) => ()) value = ()}) := by
    calc
      (1 : ENNReal) = edist (0 : Real) 1 := by norm_num
      _ ≤ Metric.ediam
          ((fun value : ↑(Set.univ : Set Bool) =>
              if value.1 then (1 : Real) else 0) ''
            {value | (fun _ : ↑(Set.univ : Set Bool) => ()) value = ()}) :=
        Metric.edist_le_ediam_of_mem
          ⟨⟨false, Set.mem_univ false⟩, by simp⟩
          ⟨⟨true, Set.mem_univ true⟩, by simp⟩
  have oneLeWorst : (1 : ENNReal) ≤
      worstFiberDefect
        (fun _ : ↑(Set.univ : Set Bool) => ())
        (fun value : ↑(Set.univ : Set Bool) =>
          if value.1 then (1 : Real) else 0) :=
    oneLeFiber.trans (le_iSup
      (fun coordinate : Unit =>
        Metric.ediam
          ((fun value : ↑(Set.univ : Set Bool) =>
              if value.1 then (1 : Real) else 0) ''
            {value | (fun _ : ↑(Set.univ : Set Bool) => ()) value = coordinate})) ())
  have : (1 : ENNReal) ≤ 0 := oneLeWorst.trans locallyComplete
  norm_num at this

/-- Quantifier control for conjunct 7. Adjacent transitions alternate between
target and precision changes, and target changes infinitely often, but no one
field changes at every stage. Thus the chosen persistent-field reading is
strictly stronger than both `forall stage, exists field` and frequent change. -/
theorem alternating_changes_are_not_open_world :
    let parameters : Nat -> LocalParameters Unit Nat Unit := fun stage =>
      { objectDomain := Set.univ
        target := fun _ => stage / 2
        operationFamily := Set.univ
        precision := (↑((stage + 1) / 2) : ENNReal) }
    (∀ stage,
      LocalParametersChanged (parameters stage) (parameters (stage + 1))) ∧
      (∃ᶠ stage in Filter.atTop,
        (parameters stage).target ≠ (parameters (stage + 1)).target) ∧
      ¬OpenWorldSequence parameters := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro stage
    rcases stage.even_or_odd' with ⟨half, rfl | rfl⟩
    · exact Or.inr (Or.inr (Or.inl (by
        norm_num
        omega)))
    · exact Or.inr (Or.inl (by
        intro targetsEqual
        have equalAtUnit := congrFun targetsEqual ()
        norm_num at equalAtUnit
        omega))
  · refine Filter.frequently_atTop.2 ?_
    intro lowerBound
    refine ⟨2 * lowerBound + 1, by omega, ?_⟩
    intro targetsEqual
    have equalAtUnit := congrFun targetsEqual ()
    omega
  · rintro (domainAlways | targetAlways | precisionAlways | operationsAlways)
    · exact domainAlways 0 rfl
    · apply targetAlways 0
      funext object
      simp
    · apply precisionAlways 1
      norm_num
    · exact operationsAlways 0 rfl

/-- Negative control for conjunct 9: a constant, locally complete parameter
sequence has neither persistent change nor any reopening. -/
theorem constant_complete_sequence_does_not_reopen :
    let parameters : Nat -> LocalParameters Unit Real Unit := fun _ =>
      { objectDomain := Set.univ
        target := fun _ => 0
        operationFamily := Set.univ
        precision := 0 }
    let languages : Nat -> Set Unit := fun _ => ∅
    let systems : Nat -> Concept Unit Real := fun _ _ => 0
    (∀ stage, LocallyComplete (parameters stage) (systems stage)) ∧
      ¬OpenWorldSequence parameters ∧
      ¬(∃ᶠ stage in Filter.atTop,
        Reopens (parameters stage) (parameters (stage + 1))
          (languages stage) (languages (stage + 1)) (systems stage)) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro stage
    unfold LocallyComplete ApproximatelyClosed worstFiberDefect
    refine iSup_le fun coordinate => Metric.ediam_image_le_iff.2 ?_
    intro first _firstInFiber second _secondInFiber
    simp
  · simp [OpenWorldSequence]
  · simp [Reopens, LocalParametersChanged]

/-- Positive finite control: the old fixed stage is closed, while a changed
Boolean target creates a genuinely new canonical defect. -/
example :
    let current : LocalParameters Bool Bool Unit :=
      { objectDomain := Set.univ
        target := fun _ => false
        operationFamily := Set.univ
        precision := 0 }
    let next : LocalParameters Bool Bool Unit :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := 0 }
    Closed (fun _object : ↑current.objectDomain => false)
        (fun object : ↑current.objectDomain => current.target object.1) ∧
      Reopens current next (∅ : Set Unit) ∅ (fun _ => false) := by
  dsimp
  constructor
  · ext pair
    simp [defectRelation]
  · constructor
    · refine Or.inl (Or.inr (Or.inl ?_))
      intro equalTargets
      exact Bool.false_ne_true (congrFun equalTargets true)
    · exact ⟨(false, true), by simp [defectRelation]⟩

/-- Named negative control for conjunct 8: precision changes and both canonical
defect sets are equal and nonempty, so no genuinely new defect exists. -/
theorem precision_change_without_new_defect_does_not_reopen :
    let current : LocalParameters Bool Bool Unit :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := 0 }
    let next : LocalParameters Bool Bool Unit :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := 1 }
    let readout : Concept Bool Bool := fun _ => false
    LocalParametersChanged current next ∧
      ((defectRelation readout next.target ∩
          (next.objectDomain ×ˢ next.objectDomain)) =
        (defectRelation readout current.target ∩
          (current.objectDomain ×ˢ current.objectDomain))) ∧
      (defectRelation readout next.target ∩
        (next.objectDomain ×ˢ next.objectDomain)).Nonempty ∧
      ¬Reopens current next (∅ : Set Unit) ∅ readout := by
  dsimp
  refine ⟨Or.inr (Or.inr (Or.inl zero_ne_one)), rfl, ?_, ?_⟩
  · exact ⟨(false, true), by simp [defectRelation]⟩
  · simp [Reopens]

/-- False-side finite example reusing the named genuine-reopening control. -/
example :
    let current : LocalParameters Bool Bool Unit :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := 0 }
    let next : LocalParameters Bool Bool Unit :=
      { objectDomain := Set.univ
        target := id
        operationFamily := Set.univ
        precision := 1 }
    let readout : Concept Bool Bool := fun _ => false
    LocalParametersChanged current next ∧
      ((defectRelation readout next.target ∩
          (next.objectDomain ×ˢ next.objectDomain)) =
        (defectRelation readout current.target ∩
          (current.objectDomain ×ˢ current.objectDomain))) ∧
      (defectRelation readout next.target ∩
        (next.objectDomain ×ˢ next.objectDomain)).Nonempty ∧
      ¬Reopens current next (∅ : Set Unit) ∅ readout :=
  precision_change_without_new_defect_does_not_reopen

#print axioms stopping_continuation_reopening

end D5.S3.ConceptDynamics.Termination.StoppingContinuationReopening
