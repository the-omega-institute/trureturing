/- GID: D5/S3/ConceptDynamics/Termination/ClosureMethodStopThreeParameterCompletionReopening
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Termination/ClosureMethodStopThreeParameterCompletionReopening
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact/approximate closure, method stop, and three-parameter completion/reopening. -/

import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
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
   * Domain search `rg -n 'NNReal|ℝ≥0|precision : ENNReal|coe_ne_top' D5/S3/
     ConceptDynamics .lake/packages/mathlib/Mathlib -g '*.lean'` found existing
     `NNReal` budget use and the exact boundary lemma `ENNReal.coe_ne_top`.
     Source check `nl -ba docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md |
     sed -n '1038,1080p'` found that section 9.1 assumes a metric and explicitly
     uses `eta = 0`, but gives `eta` no type and does not decide negative
     tolerances. This module chooses finite `NNReal` tolerances as a convention;
     the supremum remains extended when a target fiber is unbounded.
   * Neighbor vocabulary `ls D5/S3/ConceptDynamics/Termination` and
     `git grep -n '^def \|^  def ' -- D5/S3/ConceptDynamics | head -80` found no
     reusable local-completion or genuine-reopening definition. Source search for
     `操作族|operationFamily|definition language|定义语言|NoProposal|E_S` found
     no rule connecting operation family or definition language to the section-43
     residual, and no signature for the method symbol beyond its displayed
     equation. Those two unsupported reopening triggers are recorded below as
     unresolved source gaps instead of decorative parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Termination.ClosureMethodStopThreeParameterCompletionReopening

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
    (precision : NNReal) : Prop :=
  worstFiberDefect readout target ≤ (precision : ENNReal)

/-- Method stopping is the literal distinguished-value equation in section 43. -/
def MethodStopped {System Evidence Proposal : Type*}
    (method : System -> Evidence -> Proposal)
    (system : System) (evidence : Evidence) (noProposal : Proposal) : Prop :=
  method system evidence = noProposal

/-- The parameters whose effect on section-43 closure is defined. The source does
not type its tolerance or decide negative values; this interface conventionally
chooses finite nonnegative real precision. -/
structure ThreeParameterLocalParameters (World Target : Type*) where
  objectDomain : Set World
  target : Concept World Target
  precision : NNReal

/-- Local completion checks approximate target closure on the supplied object
domain at the supplied finite precision. -/
def ThreeParameterLocallyComplete
    {World Coordinate Target : Type*} [MetricSpace Target]
    (parameters : ThreeParameterLocalParameters World Target)
    (readout : Concept World Coordinate) : Prop :=
  ApproximatelyClosed
    (fun object : ↑parameters.objectDomain => readout object.1)
    (fun object : ↑parameters.objectDomain => parameters.target object.1)
    parameters.precision

/-- At least one parameter with a defined residual effect changes. -/
def ThreeParameterLocalParametersChanged
    {World Target : Type*}
    (current next : ThreeParameterLocalParameters World Target) : Prop :=
  current.objectDomain ≠ next.objectDomain ∨
    current.target ≠ next.target ∨
    current.precision ≠ next.precision

/-- Reopening requires a supported parameter change and a genuinely new
precision-filtered canonical target defect: a pair present after the change but
absent before it. Each stage uses its own precision. Both sets are expressed in
the ambient world so domain changes compare.

Unresolved source gaps: DECT section 5 defines a language-blind residual and
section 44 defines operation-induced observational equivalence, but section 43
does not identify either construction with its `q_S` or `E_S(T)`, nor give a
transition map to a new stage residual. Operation-family and definition-language
changes are therefore absent from this interface; this definition covers only
object-domain, target, and precision triggers. -/
def ThreeParameterReopens
    {World Coordinate Target : Type*}
    [MetricSpace Target]
    (current next : ThreeParameterLocalParameters World Target)
    (readout : Concept World Coordinate) : Prop :=
  ThreeParameterLocalParametersChanged current next ∧
    ((((defectRelation readout next.target) ∩
            {pair | (next.precision : ENNReal) <
              edist (next.target pair.1) (next.target pair.2)}) ∩
          (next.objectDomain ×ˢ next.objectDomain)) \
      (((defectRelation readout current.target) ∩
            {pair | (current.precision : ENNReal) <
              edist (current.target pair.1) (current.target pair.2)}) ∩
          (current.objectDomain ×ˢ current.objectDomain))).Nonempty

/-- The five formalized assertions in one public package. The reopening clause
covers the three source triggers with a defined residual effect; operation-family
and definition-language triggers remain unresolved source gaps. Budget stopping
and open-world sequence were removed after fidelity review; see issue #3157. -/
theorem closure_method_stop_three_parameter_completion_reopening :
    (∀ {X Coordinate Target : Type*}
      (readout : Concept X Coordinate) (target : Concept X Target),
      Closed readout target ↔ defectRelation readout target = ∅) ∧
    (∀ {X Coordinate Target : Type*} [MetricSpace Target]
      (readout : Concept X Coordinate) (target : Concept X Target)
      (precision : NNReal),
      ApproximatelyClosed readout target precision ↔
        worstFiberDefect readout target ≤ (precision : ENNReal)) ∧
    (∀ {System Evidence Proposal : Type*}
      (method : System -> Evidence -> Proposal)
      (system : System) (evidence : Evidence) (noProposal : Proposal),
      MethodStopped method system evidence noProposal ↔
        method system evidence = noProposal) ∧
    (∀ {World Coordinate Target : Type*} [MetricSpace Target]
      (parameters : ThreeParameterLocalParameters World Target)
      (readout : Concept World Coordinate),
      ThreeParameterLocallyComplete parameters readout ↔
        ApproximatelyClosed
          (fun object : ↑parameters.objectDomain => readout object.1)
          (fun object : ↑parameters.objectDomain => parameters.target object.1)
          parameters.precision) ∧
    (∀ {World Coordinate Target : Type*}
      [MetricSpace Target]
      (current next : ThreeParameterLocalParameters World Target)
      (readout : Concept World Coordinate),
      ThreeParameterReopens current next readout ↔
        ThreeParameterLocalParametersChanged current next ∧
          ((((defectRelation readout next.target) ∩
                  {pair | (next.precision : ENNReal) <
                    edist (next.target pair.1) (next.target pair.2)}) ∩
                (next.objectDomain ×ˢ next.objectDomain)) \
            (((defectRelation readout current.target) ∩
                  {pair | (current.precision : ENNReal) <
                    edist (current.target pair.1) (current.target pair.2)}) ∩
                (current.objectDomain ×ˢ current.objectDomain))).Nonempty) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
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

/-- Negative control for conjunct 3: returning a proposal is not method stop. -/
theorem proposal_return_is_not_method_stopped :
    ¬MethodStopped (fun _ : Unit => id) () true false := by
  simp [MethodStopped]

private abbrev ZeroPrecisionNonconstantFiberControl : Prop :=
    let parameters : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := fun value => if value then 1 else 0
        precision := 0 }
    ¬ThreeParameterLocallyComplete parameters (fun _ => ())

/-- Negative control for conjunct 4: local completion reads the supplied zero
precision and rejects a nonconstant target on one readout fiber. -/
theorem zero_precision_nonconstant_fiber_is_not_locally_complete :
    ZeroPrecisionNonconstantFiberControl := by
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

private abbrev ChangedTargetReopeningControl : Prop :=
    let current : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := fun _ => 0
        precision := 0 }
    let next : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := fun value => if value then 1 else 0
        precision := 0 }
    Closed (fun _object : ↑current.objectDomain => ())
        (fun object : ↑current.objectDomain => current.target object.1) ∧
      ThreeParameterReopens current next (fun _ => ())

/-- Positive finite control: the old fixed stage is closed, while a changed
Boolean target creates a genuinely new canonical defect. -/
theorem changed_target_creates_genuine_reopening :
    ChangedTargetReopeningControl := by
  constructor
  · ext pair
    simp [defectRelation]
  · constructor
    · refine Or.inr (Or.inl ?_)
      intro equalTargets
      have := congrFun equalTargets true
      norm_num at this
    · exact ⟨(false, true), by simp [defectRelation]⟩

private abbrev ObjectDomainExpansionReopeningControl : Prop :=
    let target : Concept Bool Real := fun value => if value then 1 else 0
    let current : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := {false}
        target := target
        precision := 0 }
    let next : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := target
        precision := 0 }
    current.target = next.target ∧
    current.precision = next.precision ∧
      current.objectDomain ⊂ next.objectDomain ∧
      ThreeParameterReopens current next (fun _ => ())

/-- Object-domain-only reopening control: the target and precision stay fixed,
while expanding the Boolean domain from one point to both points admits a new
canonical defect pair. -/
theorem object_domain_expansion_creates_genuine_reopening :
    ObjectDomainExpansionReopeningControl := by
  have domainStrict : ({false} : Set Bool) ⊂ Set.univ :=
    Set.ssubset_iff_exists.mpr
      ⟨Set.subset_univ _, true, Set.mem_univ true, by simp⟩
  refine ⟨rfl, rfl, domainStrict, ?_⟩
  constructor
  · exact Or.inl domainStrict.ne
  · exact ⟨(false, true), by simp [defectRelation]⟩

private abbrev NonconstantReadoutFiberGuardControl : Prop :=
    let current : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := fun _ => 0
        precision := 0 }
    let next : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := fun value => if value then 1 else 0
        precision := 0 }
    let readout : Concept Bool Bool := id
    readout false ≠ readout true ∧
      ((false, true) ∈
        ((({pair | next.precision <
            edist (next.target pair.1) (next.target pair.2)}) ∩
              (next.objectDomain ×ˢ next.objectDomain)) \
          (({pair | current.precision <
            edist (current.target pair.1) (current.target pair.2)}) ∩
              (current.objectDomain ×ˢ current.objectDomain)))) ∧
      ¬ThreeParameterReopens current next readout

/-- A nonconstant readout separates the two Boolean points. The same pair is
present in a residual that only checks distance, but it is absent from the
canonical fiber-conditioned residual, so deleting either `defectRelation`
intersection makes this named consumer fail. -/
theorem nonconstant_readout_blocks_cross_fiber_reopening :
    NonconstantReadoutFiberGuardControl := by
  refine ⟨Bool.false_ne_true, ?_, ?_⟩
  · simp
  · rintro ⟨_, ⟨⟨first, second⟩, newResidual, _⟩⟩
    simp [defectRelation] at newResidual
    exact newResidual.2 (by simpa [newResidual.1])

private abbrev PrecisionDecreaseReopeningControl : Prop :=
    let target : Concept Bool Real := fun value => if value then 1 else 0
    let current : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := target
        precision := 1 }
    let next : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := target
        precision := 0 }
    current.objectDomain = next.objectDomain ∧
      current.target = next.target ∧
      ThreeParameterReopens current next (fun _ => ())

/-- Precision-only reopening control: lowering eta from one to zero exposes a
pair at target distance one, with every other formalized parameter fixed. -/
theorem precision_decrease_creates_genuine_reopening :
    PrecisionDecreaseReopeningControl := by
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · exact Or.inr (Or.inr one_ne_zero)
  · exact ⟨(false, true), by simp [defectRelation]⟩

private abbrev PrecisionIncreaseNoReopeningControl : Prop :=
    let target : Concept Bool Real := fun value => if value then 1 else 0
    let current : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := target
        precision := 0 }
    let next : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := target
        precision := 1 }
    let readout : Concept Bool Unit := fun _ => ()
    ThreeParameterLocalParametersChanged current next ∧
      (defectRelation readout next.target).Nonempty ∧
      ¬ThreeParameterReopens current next readout

/-- Named negative control for conjunct 5: increasing precision removes rather
than creates tolerated residuals, even though the exact defect stays nonempty. -/
theorem precision_change_without_new_defect_does_not_reopen :
    PrecisionIncreaseNoReopeningControl := by
  refine ⟨Or.inr (Or.inr zero_ne_one), ?_, ?_⟩
  · exact ⟨(false, true), by simp [defectRelation]⟩
  · rintro ⟨_, ⟨⟨first, second⟩, newResidual, _⟩⟩
    fin_cases first <;> fin_cases second <;>
      norm_num [defectRelation] at newResidual

/-- Concrete finite witnesses for all five package clauses, all three supported
reopening triggers, the canonical-fiber guard, and the precision negative
neighbor. Every named control is consumed here fail-closed. -/
theorem closure_method_stop_three_parameter_completion_reopening_nonvacuity :
    (¬Closed (fun _ : Bool => ()) (id : Concept Bool Bool)) ∧
    (¬ApproximatelyClosed (fun _ : Bool => ())
      (fun value : Bool => if value then (1 : Real) else 0) 0) ∧
    (¬MethodStopped (fun _ : Unit => id) () true false) ∧
    (let parameters : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := fun value => if value then 1 else 0
        precision := 0 }
     ¬ThreeParameterLocallyComplete parameters (fun _ => ())) ∧
    (let target : Concept Bool Real := fun value => if value then 1 else 0
     let current : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := {false}
        target := target
        precision := 0 }
     let next : ThreeParameterLocalParameters Bool Real :=
      { objectDomain := Set.univ
        target := target
        precision := 0 }
     current.target = next.target ∧
       current.precision = next.precision ∧
       current.objectDomain ⊂ next.objectDomain ∧
       ThreeParameterReopens current next (fun _ => ())) ∧
    ChangedTargetReopeningControl ∧
    PrecisionDecreaseReopeningControl ∧
    NonconstantReadoutFiberGuardControl ∧
    PrecisionIncreaseNoReopeningControl := by
  exact ⟨hidden_bool_target_is_not_closed,
    positive_fiber_diameter_is_not_approximately_closed,
    proposal_return_is_not_method_stopped,
    zero_precision_nonconstant_fiber_is_not_locally_complete,
    object_domain_expansion_creates_genuine_reopening,
    changed_target_creates_genuine_reopening,
    precision_decrease_creates_genuine_reopening,
    nonconstant_readout_blocks_cross_fiber_reopening,
    precision_change_without_new_defect_does_not_reopen⟩

#print axioms closure_method_stop_three_parameter_completion_reopening
#print axioms closure_method_stop_three_parameter_completion_reopening_nonvacuity
#print axioms object_domain_expansion_creates_genuine_reopening

end D5.S3.ConceptDynamics.Termination.ClosureMethodStopThreeParameterCompletionReopening
