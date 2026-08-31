/- GID: D5/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalTuition/ResponseUpgradeWellFounded
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite T2 traces stop or change class; blind retries are decidably rejected. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic

/- Library-search audit trail (2026-08-31):
   * Repository and Mathlib searches for T2 response traces, retry
     well-foundedness, and decidable blind-retry violations found no covering
     declaration; the finite-list pigeonhole argument is proved here.
   * Clause echo: `ResponseEvent` records stimulus, class, response, and stop;
     `T2Compliant` is the defining per-stimulus/class `Nodup` predicate;
     `t2_response_upgrade_well_founded` is the finite-prefix consequence of
     the source's infinite nonrepetition clause; `t2ViolationDecision` is the
     executable violation classifier.
   * T2 is a proposition/structure field, never a Lean axiom; all finite
   carriers and witnesses are explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalTuition.ResponseUpgradeWellFounded

/-- One finite response to one stimulus.  `stopped` records the explicit stop
branch; changing `responseClass` records an upgrade to a different hypothesis
or tool class. -/
structure ResponseEvent (Stimulus ResponseClass Response : Type*) where
  stimulus : Stimulus
  responseClass : ResponseClass
  response : Response
  stopped : Bool
deriving DecidableEq, Repr

/-- The response values used for one stimulus and one response class, excluding
terminal events. -/
def retryResponses {Stimulus ResponseClass Response : Type*}
    [DecidableEq Stimulus] [DecidableEq ResponseClass]
    (trace : List (ResponseEvent Stimulus ResponseClass Response))
    (stimulus : Stimulus) (responseClass : ResponseClass) : List Response :=
  (trace.filter fun event =>
    event.stimulus == stimulus &&
      event.responseClass == responseClass && event.stopped == false).map
    ResponseEvent.response

/-- T2 is a defining trace predicate: within each finite stimulus/class slice,
nonterminal responses are pairwise nonrepeating. -/
def T2Compliant {Stimulus ResponseClass Response : Type*}
    [Fintype Stimulus] [Fintype ResponseClass]
    [DecidableEq Stimulus] [DecidableEq ResponseClass] [DecidableEq Response]
    (trace : List (ResponseEvent Stimulus ResponseClass Response)) : Prop :=
  ∀ stimulus ∈ (Finset.univ : Finset Stimulus),
    ∀ responseClass ∈ (Finset.univ : Finset ResponseClass),
      (retryResponses trace stimulus responseClass).Nodup

/-- A trajectory packages the defining T2 law as evidence rather than as an
axiom. -/
structure T2CompliantTrajectory (Stimulus ResponseClass Response : Type*)
    [Fintype Stimulus] [Fintype ResponseClass]
    [DecidableEq Stimulus] [DecidableEq ResponseClass] [DecidableEq Response]
    where
  events : List (ResponseEvent Stimulus ResponseClass Response)
  t2Compliant : T2Compliant events

/-- The executable classifier for a T2 violation.  Finiteness of all three
carriers makes the universal predicate decidable. -/
def t2ViolationDecision {Stimulus ResponseClass Response : Type*}
    [Fintype Stimulus] [Fintype ResponseClass] [DecidableEq Stimulus]
    [DecidableEq ResponseClass] [DecidableEq Response]
    (trace : List (ResponseEvent Stimulus ResponseClass Response)) : Bool :=
  letI : Decidable (T2Compliant trace) := by
    unfold T2Compliant
    infer_instance
  decide (¬ T2Compliant trace)

private theorem nodup_length_le_card
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (responses : List Response) (nodup : responses.Nodup) :
    responses.length ≤ Fintype.card Response := by
  calc
    responses.length = responses.toFinset.card :=
      (List.toFinset_card_of_nodup nodup).symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card Response := by simp

/-- T-H: a finite T2-compliant trace for one stimulus cannot keep retrying the
same response class past the response alphabet's cardinality.  Consequently,
when the whole trace is longer, some event must stop or switch class. -/
theorem t2_response_upgrade_well_founded
    {Stimulus ResponseClass Response : Type*}
    [Fintype Stimulus] [Fintype ResponseClass] [Fintype Response]
    [DecidableEq Stimulus] [DecidableEq ResponseClass] [DecidableEq Response]
    (trace : List (ResponseEvent Stimulus ResponseClass Response))
    (stimulus : Stimulus) (responseClass : ResponseClass)
    (compliant : T2Compliant trace)
    (sameStimulus : ∀ event, event ∈ trace -> event.stimulus = stimulus)
    (longTrace : Fintype.card Response < trace.length) :
    ∃ event, event ∈ trace ∧
      (event.stopped = true ∨ event.responseClass ≠ responseClass) := by
  by_contra no_upgrade
  push Not at no_upgrade
  have all_retries : ∀ event, event ∈ trace ->
      event.stopped = false ∧ event.responseClass = responseClass := by
    intro event eventMem
    have noStop := no_upgrade event eventMem
    have stoppedFalse : event.stopped = false := by
      have stoppedNe : event.stopped ≠ true := noStop.1
      cases stopped : event.stopped <;> simp_all
    have sameClass : event.responseClass = responseClass := by
      exact noStop.2
    exact ⟨stoppedFalse, sameClass⟩
  have filter_eq :
      trace.filter (fun event =>
        event.stimulus == stimulus &&
          event.responseClass == responseClass && event.stopped == false) = trace := by
    apply List.filter_eq_self.mpr
    intro event eventMem
    simp [sameStimulus event eventMem, (all_retries event eventMem).2,
      (all_retries event eventMem).1]
  have retryNodup :
      ((trace.filter (fun event =>
        event.stimulus == stimulus &&
          event.responseClass == responseClass && event.stopped == false)).map
        ResponseEvent.response).Nodup :=
    compliant stimulus (Finset.mem_univ _) responseClass (Finset.mem_univ _)
  rw [filter_eq] at retryNodup
  have lengthBound :
      (trace.map ResponseEvent.response).length ≤ Fintype.card Response :=
    nodup_length_le_card _ retryNodup
  have longMapped :
      Fintype.card Response < (trace.map ResponseEvent.response).length := by
    simpa using longTrace
  exact (Nat.not_lt_of_ge lengthBound longMapped)

/-- The Boolean classifier agrees exactly with the T2-violation proposition. -/
theorem t2_violation_decidable
    {Stimulus ResponseClass Response : Type*}
    [Fintype Stimulus] [Fintype ResponseClass]
    [DecidableEq Stimulus] [DecidableEq ResponseClass] [DecidableEq Response]
    (trace : List (ResponseEvent Stimulus ResponseClass Response)) :
    t2ViolationDecision trace = true ↔ ¬ T2Compliant trace := by
  letI : Decidable (T2Compliant trace) := by
    unfold T2Compliant
    infer_instance
  simp [t2ViolationDecision]

#print axioms t2_response_upgrade_well_founded
#print axioms t2_violation_decidable

-- A concrete blind retry repeats the sole response of a one-element alphabet.
private def sampleEvent : ResponseEvent Unit Unit (Fin 1) where
  stimulus := ()
  responseClass := ()
  response := 0
  stopped := false

private def sampleBlindRetry : List (ResponseEvent Unit Unit (Fin 1)) :=
  [sampleEvent, sampleEvent]

example : T2CompliantTrajectory Unit Unit (Fin 1) := by
  refine { events := [], t2Compliant := ?_ }
  intro stimulus stimulusMem responseClass responseClassMem
  simp [retryResponses]

example : t2ViolationDecision sampleBlindRetry = true := by
  decide

example : ¬ T2Compliant sampleBlindRetry := by
  intro compliant
  have nodup := compliant () (Finset.mem_univ _) () (Finset.mem_univ _)
  simp [retryResponses, sampleBlindRetry, sampleEvent] at nodup

end D5.S3.ConceptDynamics.OperationalTuition.ResponseUpgradeWellFounded
