/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/PartialDiagramEventRowCompilerSoundness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/PartialDiagramEventRowCompilerSoundness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observational, interventional, and counterfactual event probabilities compile to exact rational rows over admissible completion-signature atoms. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialDiagramConstraintCompilerSoundness
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * `PartialDiagramConstraintCompilerSoundness` exactly characterizes normalized
     mixtures supported on graph completions compatible with required edges,
     forbidden edges, and a query-order side condition. It does not encode
     observed or interventional event probabilities.
   * `CanonicalResponseSignature` and `CausalOrderLinearProgram` show that a
     Boolean response event is a zero-one linear objective, but they do not
     combine such rows with partial-diagram completion uncertainty.
   * Repository searches found no joint completion-signature carrier whose
     generated LP is equivalent to both admissible support and exact finite
     observational, interventional, or counterfactual event marginals.
   * The compiler below remains in the linear lane. Polynomial mediator
     factorizations and other cross-world independence equations remain outside
     this truth source. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialDiagramEventRowCompilerSoundness

open scoped BigOperators
open D5.S0.Certificates.LinearObjectiveDual
open D5.S3.ConceptDynamics.Causal.FiniteLinearCausalIdentification
open D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialGraphInformationOrder
open D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialDiagramConstraintCompilerSoundness

/-- Semantic kind of a finite causal event. This records what the event means,
independently of the provenance layer that justifies using its probability. -/
inductive CausalEventKind where
  | observational
  | interventional
  | counterfactual
  deriving DecidableEq, Repr

/-- Finite event information available to the compiler. `kind` records event
semantics, while `layer` records whether the numerical constraint is treated as
data, a structural consequence, or a sensitivity assumption. -/
structure EventObservation
    (Completion Signature Event : Type*) where
  kind : Event -> CausalEventKind
  layer : Event -> ConstraintLayer
  holds : Event -> Completion -> Signature -> Bool
  target : Event -> ℚ

/-- One atom of the joint response law records both the selected graph
completion and the deterministic response signature. -/
abbrev CompletionSignatureAtom
    (Completion Signature : Type*) := Completion × Signature

/-- Probability of a Boolean event under a finite joint law on completion and
response-signature atoms. -/
def jointEventMass
    {Completion Signature : Type*}
    [Fintype Completion] [Fintype Signature]
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (event : Completion -> Signature -> Bool) : ℚ :=
  ∑ atom, if event atom.1 atom.2 then mass atom else 0

/-- Generated rows. Probability normalization is represented by two rows;
every inadmissible joint atom receives a zero-support row; and every supplied
event probability is represented by paired upper and lower rows. -/
inductive EventRowConstraint
    (Node Completion Signature Event : Type*)
  | atomNonnegative (completion : Completion) (signature : Signature)
  | totalUpper
  | totalLower
  | requiredViolation
      (completion : Completion) (signature : Signature)
      (source target : Node)
  | forbiddenViolation
      (completion : Completion) (signature : Signature)
      (source target : Node)
  | queryOrderViolation
      (completion : Completion) (signature : Signature)
  | eventUpper (event : Event)
  | eventLower (event : Event)
  deriving DecidableEq, Fintype

/-- Exact rational coefficient matrix for the joint support-and-event compiler. -/
noncomputable def eventRow
    {Node Completion Signature Event : Type*}
    [DecidableEq Completion] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event) :
    EventRowConstraint Node Completion Signature Event ->
      CompletionSignatureAtom Completion Signature -> ℚ := by
  classical
  intro constraint candidate
  cases constraint with
  | atomNonnegative completion signature =>
      exact if candidate = (completion, signature) then -1 else 0
  | totalUpper =>
      exact 1
  | totalLower =>
      exact -1
  | requiredViolation completion signature source target =>
      exact
        if RequiredViolation diagram completionSemantics
            completion source target then
          if candidate = (completion, signature) then 1 else 0
        else 0
  | forbiddenViolation completion signature source target =>
      exact
        if ForbiddenViolation diagram completionSemantics
            completion source target then
          if candidate = (completion, signature) then 1 else 0
        else 0
  | queryOrderViolation completion signature =>
      exact
        if ¬ completionSemantics.queryOrderCompatible completion then
          if candidate = (completion, signature) then 1 else 0
        else 0
  | eventUpper event =>
      exact if observation.holds event candidate.1 candidate.2 then 1 else 0
  | eventLower event =>
      exact if observation.holds event candidate.1 candidate.2 then -1 else 0

/-- Right-hand side of every generated row. -/
def eventRhs
    {Node Completion Signature Event : Type*}
    (observation : EventObservation Completion Signature Event) :
    EventRowConstraint Node Completion Signature Event -> ℚ
  | .atomNonnegative _ _ => 0
  | .totalUpper => 1
  | .totalLower => -1
  | .requiredViolation _ _ _ _ => 0
  | .forbiddenViolation _ _ _ _ => 0
  | .queryOrderViolation _ _ => 0
  | .eventUpper event => observation.target event
  | .eventLower event => -observation.target event

/-- Provenance layer of each row. Support and normalization rows are structural;
event rows retain their explicitly supplied provenance. -/
def eventLayer
    {Node Completion Signature Event : Type*}
    (observation : EventObservation Completion Signature Event) :
    EventRowConstraint Node Completion Signature Event -> ConstraintLayer
  | .eventUpper event => observation.layer event
  | .eventLower event => observation.layer event
  | _ => .structural

/-- The exact finite causal LP generated from a partial diagram, a finite event
table, and an arbitrary rational query coefficient. -/
noncomputable def eventConstrainedProblem
    {Node Completion Signature Event : Type*}
    [Fintype Node] [DecidableEq Node]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    [Fintype Event] [DecidableEq Event]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (queryCoefficient : CompletionSignatureAtom Completion Signature -> ℚ) :
    FiniteLinearCausalProblem
      (CompletionSignatureAtom Completion Signature)
      (EventRowConstraint Node Completion Signature Event) where
  layer := eventLayer observation
  row := eventRow diagram completionSemantics observation
  rhs := eventRhs observation
  queryCoefficient := queryCoefficient

@[simp] theorem atomNonnegativeRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (completion : Completion) (signature : Signature) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (.atomNonnegative completion signature) candidate * mass candidate) =
      -mass (completion, signature) := by
  classical
  simp [eventRow]

@[simp] theorem totalUpperEventRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (EventRowConstraint.totalUpper :
          EventRowConstraint Node Completion Signature Event)
        candidate * mass candidate) =
      ∑ candidate, mass candidate := by
  classical
  simp [eventRow]

@[simp] theorem totalLowerEventRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (EventRowConstraint.totalLower :
          EventRowConstraint Node Completion Signature Event)
        candidate * mass candidate) =
      -(∑ candidate, mass candidate) := by
  classical
  simp [eventRow, Finset.sum_neg_distrib]

@[simp] theorem requiredViolationEventRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (completion : Completion) (signature : Signature)
    (source target : Node) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (.requiredViolation completion signature source target) candidate *
        mass candidate) =
      if RequiredViolation diagram completionSemantics
          completion source target then
        mass (completion, signature)
      else 0 := by
  classical
  by_cases violation :
      RequiredViolation diagram completionSemantics completion source target
  · simp [eventRow, violation]
  · simp [eventRow, violation]

@[simp] theorem forbiddenViolationEventRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (completion : Completion) (signature : Signature)
    (source target : Node) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (.forbiddenViolation completion signature source target) candidate *
        mass candidate) =
      if ForbiddenViolation diagram completionSemantics
          completion source target then
        mass (completion, signature)
      else 0 := by
  classical
  by_cases violation :
      ForbiddenViolation diagram completionSemantics completion source target
  · simp [eventRow, violation]
  · simp [eventRow, violation]

@[simp] theorem queryOrderViolationEventRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (completion : Completion) (signature : Signature) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (.queryOrderViolation completion signature) candidate * mass candidate) =
      if ¬ completionSemantics.queryOrderCompatible completion then
        mass (completion, signature)
      else 0 := by
  classical
  by_cases violation :
      ¬ completionSemantics.queryOrderCompatible completion
  · simp [eventRow, violation]
  · simp [eventRow, violation]

@[simp] theorem eventUpperRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (event : Event) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (.eventUpper event) candidate * mass candidate) =
      jointEventMass mass (observation.holds event) := by
  classical
  unfold jointEventMass
  apply Finset.sum_congr rfl
  intro candidate _
  cases h : observation.holds event candidate.1 candidate.2 <;>
    simp [eventRow, h]

@[simp] theorem eventLowerRow_eval
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (event : Event) :
    (∑ candidate,
      eventRow diagram completionSemantics observation
        (.eventLower event) candidate * mass candidate) =
      -jointEventMass mass (observation.holds event) := by
  classical
  unfold jointEventMass
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro candidate _
  cases h : observation.holds event candidate.1 candidate.2 <;>
    simp [eventRow, h]

/-- Intended semantics of the generated program: a normalized nonnegative joint
law, supported on admissible graph completions, whose supplied event
probabilities equal their exact rational targets. -/
structure EventConstrainedCompletionLaw
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [Fintype Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ) : Prop where
  nonnegative : ∀ atom, 0 ≤ mass atom
  total : (∑ atom, mass atom) = 1
  supportAdmissible : ∀ atom,
    mass atom ≠ 0 ->
      AdmissibleCompletion diagram completionSemantics atom.1
  eventEq : ∀ event,
    jointEventMass mass (observation.holds event) = observation.target event

/-- A joint atom whose completion is inadmissible has zero mass in every
semantic event-constrained law. -/
theorem atom_mass_eq_zero_of_not_admissible
    {Node Completion Signature Event : Type*}
    [Fintype Completion] [Fintype Signature]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (law : EventConstrainedCompletionLaw
      diagram completionSemantics observation mass)
    (atom : CompletionSignatureAtom Completion Signature)
    (not_admissible :
      ¬ AdmissibleCompletion diagram completionSemantics atom.1) :
    mass atom = 0 := by
  by_contra nonzero
  exact not_admissible (law.supportAdmissible atom nonzero)

/-- Exact compiler theorem. Feasibility of the generated rational LP is
logically equivalent to the intended joint support and event-probability
semantics. -/
theorem feasible_iff_event_constrained_completion_law
    {Node Completion Signature Event : Type*}
    [Fintype Node] [DecidableEq Node]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    [Fintype Event] [DecidableEq Event]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (queryCoefficient : CompletionSignatureAtom Completion Signature -> ℚ)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ) :
    Feasible
        (eventConstrainedProblem diagram completionSemantics observation
          queryCoefficient)
        mass <->
      EventConstrainedCompletionLaw
        diagram completionSemantics observation mass := by
  classical
  constructor
  · intro feasible
    have nonnegative : ∀ atom, 0 ≤ mass atom := by
      intro atom
      have row_bound := feasible
        (EventRowConstraint.atomNonnegative atom.1 atom.2)
      have neg_bound : -mass atom ≤ 0 := by
        simpa [Feasible, eventConstrainedProblem, eventRhs] using row_bound
      linarith
    refine
      { nonnegative := nonnegative
        total := ?_
        supportAdmissible := ?_
        eventEq := ?_ }
    · have upper_bound := feasible
        (EventRowConstraint.totalUpper :
          EventRowConstraint Node Completion Signature Event)
      have lower_bound := feasible
        (EventRowConstraint.totalLower :
          EventRowConstraint Node Completion Signature Event)
      have upper : (∑ atom, mass atom) ≤ 1 := by
        simpa [Feasible, eventConstrainedProblem, eventRhs] using upper_bound
      have lower : -(∑ atom, mass atom) ≤ -1 := by
        simpa [Feasible, eventConstrainedProblem, eventRhs] using lower_bound
      linarith
    · intro atom nonzero
      constructor
      · constructor
        · intro source target required
          cases edge_value :
              completionSemantics.edge atom.1 source target with
          | false =>
              have violation :
                  RequiredViolation diagram completionSemantics
                    atom.1 source target :=
                ⟨required, edge_value⟩
              have row_bound := feasible
                (EventRowConstraint.requiredViolation
                  atom.1 atom.2 source target)
              have mass_nonpositive : mass atom ≤ 0 := by
                simpa [Feasible, eventConstrainedProblem, eventRhs, violation]
                  using row_bound
              have mass_zero : mass atom = 0 :=
                le_antisymm mass_nonpositive (nonnegative atom)
              exact (nonzero mass_zero).elim
          | true =>
              simpa [completionRelation] using edge_value
        · intro source target forbidden edge_present
          have violation :
              ForbiddenViolation diagram completionSemantics
                atom.1 source target :=
            ⟨forbidden, by simpa [completionRelation] using edge_present⟩
          have row_bound := feasible
            (EventRowConstraint.forbiddenViolation
              atom.1 atom.2 source target)
          have mass_nonpositive : mass atom ≤ 0 := by
            simpa [Feasible, eventConstrainedProblem, eventRhs, violation]
              using row_bound
          have mass_zero : mass atom = 0 :=
            le_antisymm mass_nonpositive (nonnegative atom)
          exact nonzero mass_zero
      · by_contra order_failure
        have row_bound := feasible
          (EventRowConstraint.queryOrderViolation atom.1 atom.2)
        have mass_nonpositive : mass atom ≤ 0 := by
          simpa [Feasible, eventConstrainedProblem, eventRhs, order_failure]
            using row_bound
        have mass_zero : mass atom = 0 :=
          le_antisymm mass_nonpositive (nonnegative atom)
        exact nonzero mass_zero
    · intro event
      have upper_bound := feasible (EventRowConstraint.eventUpper event)
      have lower_bound := feasible (EventRowConstraint.eventLower event)
      have upper :
          jointEventMass mass (observation.holds event) ≤
            observation.target event := by
        simpa [Feasible, eventConstrainedProblem, eventRhs] using upper_bound
      have lower :
          -jointEventMass mass (observation.holds event) ≤
            -observation.target event := by
        simpa [Feasible, eventConstrainedProblem, eventRhs] using lower_bound
      linarith
  · intro law
    unfold Feasible
    intro constraint
    cases constraint with
    | atomNonnegative completion signature =>
        have nonnegative := law.nonnegative (completion, signature)
        simpa [eventConstrainedProblem, eventRhs] using
          (neg_nonpos.mpr nonnegative)
    | totalUpper =>
        simp [eventConstrainedProblem, eventRhs, law.total]
    | totalLower =>
        simp [eventConstrainedProblem, eventRhs, law.total]
    | requiredViolation completion signature source target =>
        by_cases violation :
            RequiredViolation diagram completionSemantics
              completion source target
        · have not_admissible :
              ¬ AdmissibleCompletion diagram completionSemantics completion := by
            intro admissible
            have edge_present :=
              admissible.1.1 source target violation.1
            have false_eq_true : (false : Bool) = true :=
              violation.2.symm.trans
                (by simpa [completionRelation] using edge_present)
            exact Bool.false_ne_true false_eq_true
          have mass_zero := atom_mass_eq_zero_of_not_admissible
            diagram completionSemantics observation mass law
            (completion, signature) not_admissible
          simp [eventConstrainedProblem, eventRhs, violation, mass_zero]
        · simp [eventConstrainedProblem, eventRhs, violation]
    | forbiddenViolation completion signature source target =>
        by_cases violation :
            ForbiddenViolation diagram completionSemantics
              completion source target
        · have not_admissible :
              ¬ AdmissibleCompletion diagram completionSemantics completion := by
            intro admissible
            exact admissible.1.2 source target violation.1
              (by simpa [completionRelation] using violation.2)
          have mass_zero := atom_mass_eq_zero_of_not_admissible
            diagram completionSemantics observation mass law
            (completion, signature) not_admissible
          simp [eventConstrainedProblem, eventRhs, violation, mass_zero]
        · simp [eventConstrainedProblem, eventRhs, violation]
    | queryOrderViolation completion signature =>
        by_cases violation :
            ¬ completionSemantics.queryOrderCompatible completion
        · have not_admissible :
              ¬ AdmissibleCompletion diagram completionSemantics completion := by
            intro admissible
            exact violation admissible.2
          have mass_zero := atom_mass_eq_zero_of_not_admissible
            diagram completionSemantics observation mass law
            (completion, signature) not_admissible
          simp [eventConstrainedProblem, eventRhs, violation, mass_zero]
        · simp [eventConstrainedProblem, eventRhs, violation]
    | eventUpper event =>
        simpa [eventConstrainedProblem, eventRhs] using
          (le_of_eq (law.eventEq event))
    | eventLower event =>
        have equality :
            -jointEventMass mass (observation.holds event) =
              -observation.target event :=
          congrArg (fun value : ℚ => -value) (law.eventEq event)
        simpa [eventConstrainedProblem, eventRhs] using le_of_eq equality

/-- Push a finite exogenous law to the joint completion-signature carrier. -/
def jointPushforwardMass
    {Exogenous Completion Signature : Type*}
    [Fintype Exogenous] [DecidableEq Completion] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (completionOf : Exogenous -> Completion)
    (signatureOf : Exogenous -> Signature) :
    CompletionSignatureAtom Completion Signature -> ℚ :=
  fun atom =>
    ∑ exogenous,
      if (completionOf exogenous, signatureOf exogenous) = atom then
        mass exogenous
      else 0

/-- Direct event probability on a finite exogenous carrier. -/
def exogenousEventMass
    {Exogenous Completion Signature : Type*}
    [Fintype Exogenous]
    (mass : Exogenous -> ℚ)
    (completionOf : Exogenous -> Completion)
    (signatureOf : Exogenous -> Signature)
    (event : Completion -> Signature -> Bool) : ℚ :=
  ∑ exogenous,
    if event (completionOf exogenous) (signatureOf exogenous) then
      mass exogenous
    else 0

/-- Joint pushforward preserves total mass. -/
theorem jointPushforwardMass_total
    {Exogenous Completion Signature : Type*}
    [Fintype Exogenous]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (completionOf : Exogenous -> Completion)
    (signatureOf : Exogenous -> Signature) :
    (∑ atom, jointPushforwardMass mass completionOf signatureOf atom) =
      ∑ exogenous, mass exogenous := by
  classical
  unfold jointPushforwardMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro exogenous _
  simp

/-- Joint pushforward preserves nonnegativity. -/
theorem jointPushforwardMass_nonnegative
    {Exogenous Completion Signature : Type*}
    [Fintype Exogenous]
    [DecidableEq Completion] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (mass_nonnegative : ∀ exogenous, 0 ≤ mass exogenous)
    (completionOf : Exogenous -> Completion)
    (signatureOf : Exogenous -> Signature)
    (atom : CompletionSignatureAtom Completion Signature) :
    0 ≤ jointPushforwardMass mass completionOf signatureOf atom := by
  classical
  unfold jointPushforwardMass
  apply Finset.sum_nonneg
  intro exogenous _
  split
  · exact mass_nonnegative exogenous
  · exact le_rfl

/-- Evaluating any Boolean causal event after joint pushforward gives exactly
the event probability evaluated on the original exogenous structural states. -/
theorem joint_event_mass_pushforward
    {Exogenous Completion Signature : Type*}
    [Fintype Exogenous]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (completionOf : Exogenous -> Completion)
    (signatureOf : Exogenous -> Signature)
    (event : Completion -> Signature -> Bool) :
    jointEventMass
        (jointPushforwardMass mass completionOf signatureOf) event =
      exogenousEventMass mass completionOf signatureOf event := by
  classical
  unfold jointEventMass jointPushforwardMass exogenousEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro exogenous _
  cases h : event (completionOf exogenous) (signatureOf exogenous) <;>
    simp [h]

/-- The joint atom carrier itself is a canonical finite exogenous realization
of every joint law, preserving all event probabilities definitionally. -/
theorem identity_exogenous_event_mass
    {Completion Signature : Type*}
    [Fintype Completion] [Fintype Signature]
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (event : Completion -> Signature -> Bool) :
    exogenousEventMass mass (fun atom => atom.1) (fun atom => atom.2) event =
      jointEventMass mass event := by
  rfl

/-- Every event target enforced by a feasible compiled program is realized by
the canonical identity exogenous law on completion-signature atoms. -/
theorem compiled_event_targets_have_identity_realization
    {Node Completion Signature Event : Type*}
    [Fintype Node] [DecidableEq Node]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    [Fintype Event] [DecidableEq Event]
    (diagram : PartialCausalDiagram Node)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (queryCoefficient : CompletionSignatureAtom Completion Signature -> ℚ)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (feasible : Feasible
      (eventConstrainedProblem diagram completionSemantics observation
        queryCoefficient) mass)
    (event : Event) :
    exogenousEventMass mass (fun atom => atom.1) (fun atom => atom.2)
        (observation.holds event) =
      observation.target event := by
  have law :=
    (feasible_iff_event_constrained_completion_law
      diagram completionSemantics observation queryCoefficient mass).mp feasible
  simpa [identity_exogenous_event_mass] using law.eventEq event

/-- Stronger partial-diagram information preserves every event row while
shrinking the admissible completion support. Hence its compiled feasible set is
contained in the weaker compiled feasible set. -/
theorem feasible_antitone_under_diagram_refinement
    {Node Completion Signature Event : Type*}
    [Fintype Node] [DecidableEq Node]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    [Fintype Event] [DecidableEq Event]
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (queryCoefficient : CompletionSignatureAtom Completion Signature -> ℚ)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (stronger_feasible : Feasible
      (eventConstrainedProblem stronger completionSemantics observation
        queryCoefficient) mass) :
    Feasible
      (eventConstrainedProblem weaker completionSemantics observation
        queryCoefficient) mass := by
  have stronger_law :=
    (feasible_iff_event_constrained_completion_law
      stronger completionSemantics observation queryCoefficient mass).mp
      stronger_feasible
  apply
    (feasible_iff_event_constrained_completion_law
      weaker completionSemantics observation queryCoefficient mass).mpr
  refine
    { nonnegative := stronger_law.nonnegative
      total := stronger_law.total
      supportAdmissible := ?_
      eventEq := stronger_law.eventEq }
  intro atom nonzero
  have admissible := stronger_law.supportAdmissible atom nonzero
  exact
    ⟨compatible_antitone stronger weaker refinement
        (completionRelation completionSemantics atom.1) admissible.1,
      admissible.2⟩

/-- A lower dual certificate for the weaker partial diagram remains a valid
bound for every mass feasible under a stronger diagram. -/
theorem lower_bound_survives_diagram_refinement
    {Node Completion Signature Event : Type*}
    [Fintype Node] [DecidableEq Node]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    [Fintype Event] [DecidableEq Event]
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (queryCoefficient : CompletionSignatureAtom Completion Signature -> ℚ)
    (lower : ℚ)
    (certificate : LowerCertificate
      (eventConstrainedProblem weaker completionSemantics observation
        queryCoefficient) lower)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (stronger_feasible : Feasible
      (eventConstrainedProblem stronger completionSemantics observation
        queryCoefficient) mass) :
    lower ≤ Query
      (eventConstrainedProblem stronger completionSemantics observation
        queryCoefficient) mass := by
  have weaker_feasible := feasible_antitone_under_diagram_refinement
    stronger weaker refinement completionSemantics observation
    queryCoefficient mass stronger_feasible
  have bound := query_lower_bound_of_certificate
    (eventConstrainedProblem weaker completionSemantics observation
      queryCoefficient)
    lower certificate mass weaker_feasible
  simpa [Query, eventConstrainedProblem] using bound

/-- The corresponding upper-bound certificate also survives refinement. -/
theorem upper_bound_survives_diagram_refinement
    {Node Completion Signature Event : Type*}
    [Fintype Node] [DecidableEq Node]
    [Fintype Completion] [DecidableEq Completion]
    [Fintype Signature] [DecidableEq Signature]
    [Fintype Event] [DecidableEq Event]
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (completionSemantics : CompletionSemantics Node Completion)
    (observation : EventObservation Completion Signature Event)
    (queryCoefficient : CompletionSignatureAtom Completion Signature -> ℚ)
    (upper : ℚ)
    (certificate : UpperCertificate
      (eventConstrainedProblem weaker completionSemantics observation
        queryCoefficient) upper)
    (mass : CompletionSignatureAtom Completion Signature -> ℚ)
    (stronger_feasible : Feasible
      (eventConstrainedProblem stronger completionSemantics observation
        queryCoefficient) mass) :
    Query
      (eventConstrainedProblem stronger completionSemantics observation
        queryCoefficient) mass ≤ upper := by
  have weaker_feasible := feasible_antitone_under_diagram_refinement
    stronger weaker refinement completionSemantics observation
    queryCoefficient mass stronger_feasible
  have bound := query_upper_bound_of_certificate
    (eventConstrainedProblem weaker completionSemantics observation
      queryCoefficient)
    upper certificate mass weaker_feasible
  simpa [Query, eventConstrainedProblem] using bound

/-- Every event kind is one of the three explicitly audited semantic classes. -/
theorem event_kind_is_exhaustive
    {Completion Signature Event : Type*}
    (observation : EventObservation Completion Signature Event)
    (event : Event) :
    observation.kind event = CausalEventKind.observational \/
      observation.kind event = CausalEventKind.interventional \/
      observation.kind event = CausalEventKind.counterfactual := by
  cases observation.kind event <;> simp

#print axioms feasible_iff_event_constrained_completion_law
#print axioms joint_event_mass_pushforward
#print axioms compiled_event_targets_have_identity_realization
#print axioms feasible_antitone_under_diagram_refinement
#print axioms lower_bound_survives_diagram_refinement
#print axioms upper_bound_survives_diagram_refinement

end D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialDiagramEventRowCompilerSoundness
