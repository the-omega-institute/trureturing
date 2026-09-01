/- GID: D5/S0/Automata/DFAOStateLowerBound
   generality: G
   mirror-B: D5/B/S0/Automata/DFAOStateLowerBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite distinguishing continuations certify state lower bounds for output automata built on Mathlib DFA. -/

import Mathlib.Computability.MyhillNerode

/- Library-search audit trail (2026-09-01):
   * Pinned Mathlib supplies `DFA`, its evaluation and append laws, regular
     languages, left quotients, and the Myhill-Nerode theorem. This file extends
     that upstream carrier only by the output map needed for DFAO problems.
   * Repository searches found no `DFAO`, Moore-machine output semantics,
     sparse-domain correctness predicate, or finite distinguishing-continuation
     lower-bound certificate.
   * The state lower bound below is proof carrying: a finite family of prefixes
     and pair-specific legal continuations forces their reached states to be
     distinct in every machine correct on the declared domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.DFAOStateLowerBound

universe u v w z

/-- A deterministic finite automaton with an output attached to every state.
The transition carrier is Mathlib's canonical `DFA`. -/
structure DFAO (Alphabet : Type u) (Output : Type v) (State : Type w)
    extends DFA Alphabet State where
  output : State -> Output

namespace DFAO

/-- Evaluate a word from the upstream DFA start state and read the reached
state's output. -/
def evalOutput {Alphabet : Type u} {Output : Type v} {State : Type w}
    (machine : DFAO Alphabet Output State) (word : List Alphabet) : Output :=
  machine.output (machine.toDFA.eval word)

/-- Correctness of an output automaton on an explicitly declared input domain. -/
def CorrectOn {Alphabet : Type u} {Output : Type v} {State : Type w}
    (machine : DFAO Alphabet Output State)
    (domain : Set (List Alphabet)) (target : List Alphabet -> Output) : Prop :=
  forall ⦃word⦄, word ∈ domain -> machine.evalOutput word = target word

/-- Turn a DFAO into Mathlib's Boolean-acceptance DFA by declaring which output
values are accepting. -/
def acceptBy {Alphabet : Type u} {Output : Type v} {State : Type w}
    (machine : DFAO Alphabet Output State) (accepted : Set Output) :
    DFA Alphabet State :=
  { machine.toDFA with accept := machine.output ⁻¹' accepted }

@[simp]
theorem mem_acceptBy_iff {Alphabet : Type u} {Output : Type v}
    {State : Type w} (machine : DFAO Alphabet Output State)
    (accepted : Set Output) (word : List Alphabet) :
    word ∈ (machine.acceptBy accepted).accepts <->
      machine.evalOutput word ∈ accepted := by
  rfl

/-- Global output correctness transports a DFAO directly to the corresponding
Mathlib language, so upstream regular-language and Myhill-Nerode results apply. -/
theorem accepts_acceptBy_eq_of_correct_everywhere
    {Alphabet : Type u} {Output : Type v} {State : Type w}
    (machine : DFAO Alphabet Output State)
    (target : List Alphabet -> Output) (accepted : Set Output)
    (correct : forall word, machine.evalOutput word = target word) :
    (machine.acceptBy accepted).accepts =
      {word | target word ∈ accepted} := by
  ext word
  change machine.evalOutput word ∈ accepted <->
    target word ∈ accepted
  rw [correct word]

end DFAO

/-- A finite distinguishing-continuation certificate for a target output
function on a possibly sparse input domain. -/
structure DistinguishingFamily
    {Alphabet : Type u} {Output : Type v}
    (domain : Set (List Alphabet)) (target : List Alphabet -> Output)
    (Index : Type z) where
  prefix : Index -> List Alphabet
  continuation : Index -> Index -> List Alphabet
  left_mem : forall ⦃i j⦄, i ≠ j ->
    prefix i ++ continuation i j ∈ domain
  right_mem : forall ⦃i j⦄, i ≠ j ->
    prefix j ++ continuation i j ∈ domain
  target_ne : forall ⦃i j⦄, i ≠ j ->
    target (prefix i ++ continuation i j) ≠
      target (prefix j ++ continuation i j)

/-- Any DFAO correct on the certified domain has at least as many states as
the finite distinguishing family has indices. -/
theorem state_lower_bound_of_distinguishing_family
    {Alphabet : Type u} {Output : Type v} {State : Type w}
    {Index : Type z} [Fintype State] [Fintype Index]
    (machine : DFAO Alphabet Output State)
    (domain : Set (List Alphabet)) (target : List Alphabet -> Output)
    (certificate : DistinguishingFamily domain target Index)
    (correct : machine.CorrectOn domain target) :
    Fintype.card Index <= Fintype.card State := by
  refine Fintype.card_le_of_injective
    (fun i : Index => machine.toDFA.eval (certificate.prefix i)) ?_
  intro i j sameState
  by_contra distinct
  have leftCorrect :
      machine.evalOutput
          (certificate.prefix i ++ certificate.continuation i j) =
        target (certificate.prefix i ++ certificate.continuation i j) :=
    correct (certificate.left_mem distinct)
  have rightCorrect :
      machine.evalOutput
          (certificate.prefix j ++ certificate.continuation i j) =
        target (certificate.prefix j ++ certificate.continuation i j) :=
    correct (certificate.right_mem distinct)
  apply certificate.target_ne distinct
  calc
    target (certificate.prefix i ++ certificate.continuation i j) =
        machine.evalOutput
          (certificate.prefix i ++ certificate.continuation i j) :=
      leftCorrect.symm
    _ = machine.evalOutput
          (certificate.prefix j ++ certificate.continuation i j) := by
      unfold DFAO.evalOutput
      apply congrArg machine.output
      change
        machine.toDFA.evalFrom machine.toDFA.start
            (certificate.prefix i ++ certificate.continuation i j) =
          machine.toDFA.evalFrom machine.toDFA.start
            (certificate.prefix j ++ certificate.continuation i j)
      rw [machine.toDFA.evalFrom_of_append,
        machine.toDFA.evalFrom_of_append]
      change
        machine.toDFA.evalFrom
            (machine.toDFA.eval (certificate.prefix i))
            (certificate.continuation i j) =
          machine.toDFA.evalFrom
            (machine.toDFA.eval (certificate.prefix j))
            (certificate.continuation i j)
      rw [sameState]
    _ = target (certificate.prefix j ++ certificate.continuation i j) :=
      rightCorrect

/-- A globally correct finite-state DFAO induces only finitely many upstream
Myhill-Nerode left quotients for every output predicate. -/
theorem finite_leftQuotients_of_finite_dfao
    {Alphabet : Type u} {Output : Type v} {State : Type w}
    [Fintype State] (machine : DFAO Alphabet Output State)
    (target : List Alphabet -> Output) (accepted : Set Output)
    (correct : forall word, machine.evalOutput word = target word) :
    (Set.range
      ({word | target word ∈ accepted} : Language Alphabet).leftQuotient).Finite := by
  have regular :
      ({word | target word ∈ accepted} : Language Alphabet).IsRegular := by
    rw [← machine.accepts_acceptBy_eq_of_correct_everywhere
      target accepted correct]
    exact Language.isRegular_iff.mpr
      ⟨State, inferInstance, machine.acceptBy accepted, rfl⟩
  exact regular.finite_range_leftQuotient

#print axioms state_lower_bound_of_distinguishing_family
#print axioms finite_leftQuotients_of_finite_dfao

end D5.S0.Automata.DFAOStateLowerBound
