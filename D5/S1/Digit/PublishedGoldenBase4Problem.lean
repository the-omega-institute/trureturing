/- GID: D5/S1/Digit/PublishedGoldenBase4Problem
   generality: I
   mirror-B: D5/B/S1/Digit/PublishedGoldenBase4Problem
   mirror-E: none(waiver:published-instance-semantics)
   anchors: []
   digest: The published base-four golden-ratio DFAO problem is the typed sparse problem with an explicit start-state zero loop and zero-output anchor. -/

import D5.S0.Automata.ZeroInvariantTypedDFAO
import D5.S1.Digit.GoldenDFAOMinimalityTargets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.PublishedGoldenBase4Problem

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.ZeroInvariantTypedDFAO
open D5.S1.Digit.GoldenDFAOMinimalityTargets

noncomputable section

/-- The existing exact sparse base-four specification is reused verbatim. -/
abbrev problem : SparseProblem (Fin 2) (Fin 4) BinaryZeckendorfState :=
  base4Problem

/-- A machine in the class used by the published incomplete-data experiments.
Besides typed Zeckendorf transitions, it fixes the start state under input zero
and labels that state by output zero. -/
abbrev PublishedMachine (State : Type*) :=
  AnchoredZeroInvariantTypedDFAO problem.base (0 : Fin 2) (0 : Fin 4) State

/-- Global correctness on every canonical Zeckendorf encoding of `4^i`. -/
def Correct {State : Type*} (machine : PublishedMachine State) : Prop :=
  problem.Correct machine.toMachine

/-- Correctness on the first `extent` power samples. -/
def FitsPrefix {State : Type*} (extent : Nat)
    (machine : PublishedMachine State) : Prop :=
  problem.FitsPrefix extent machine.toMachine

/-- Existence of a globally correct published machine with exactly `states`
named states. -/
def HasGlobalModel (states : Nat) : Prop :=
  ∃ machine : PublishedMachine (Fin states), Correct machine

/-- Existence of a globally correct published machine using at most `bound`
states. -/
def HasGlobalModelAtMost (bound : Nat) : Prop :=
  ∃ states, states ≤ bound ∧ HasGlobalModel states

/-- Existence of a published finite-prefix model using at most `bound` states. -/
def HasPrefixModelAtMost (extent bound : Nat) : Prop :=
  ∃ states, states ≤ bound ∧
    ∃ machine : PublishedMachine (Fin states), FitsPrefix extent machine

/-- The distinguished zero input is part of the formal machine semantics, not
an external convention attached only to a solver. -/
@[simp] theorem zero_word_output
    {State : Type*} (machine : PublishedMachine State) :
    machine.toMachine.evalOutput [(0 : Fin 2)] = some (0 : Fin 4) := by
  simpa [AnchoredZeroInvariantTypedDFAO.evalOutput] using
    AnchoredZeroInvariantTypedDFAO.evalOutput_singleton_zero machine

/-- Every globally correct bounded published machine fits every finite prefix. -/
theorem global_model_at_most_implies_prefix_model_at_most
    {extent bound : Nat} :
    HasGlobalModelAtMost bound → HasPrefixModelAtMost extent bound := by
  rintro ⟨states, hstates, machine, correct⟩
  refine ⟨states, hstates, machine, ?_⟩
  exact problem.correct_implies_fitsPrefix
    machine.toMachine correct extent

/-- Forgetting the anchor and zero-loop evidence maps the published class into
the wider typed sparse-machine class. This direction is intentionally one-way. -/
theorem hasGlobalModel_implies_typed_hasGlobalModel
    {states : Nat} :
    HasGlobalModel states → problem.HasGlobalModel states := by
  rintro ⟨machine, correct⟩
  exact ⟨machine.toMachine, correct⟩

/-- The same forgetful inclusion holds for bounded state budgets. -/
theorem hasGlobalModelAtMost_implies_typed_hasGlobalModelAtMost
    {bound : Nat} :
    HasGlobalModelAtMost bound → problem.HasGlobalModelAtMost bound := by
  rintro ⟨states, hstates, model⟩
  exact ⟨states, hstates,
    hasGlobalModel_implies_typed_hasGlobalModel model⟩

/-- A refutation of the wider typed class also excludes the published class.
The converse is not asserted: an UNSAT result using the zero-loop convention
cannot silently be promoted to the wider powers-only problem. -/
theorem no_published_global_model_at_most_of_no_typed_global_model_at_most
    {bound : Nat}
    (typedImpossible : ¬problem.HasGlobalModelAtMost bound) :
    ¬HasGlobalModelAtMost bound := by
  intro published
  exact typedImpossible
    (hasGlobalModelAtMost_implies_typed_hasGlobalModelAtMost published)

#print axioms zero_word_output
#print axioms global_model_at_most_implies_prefix_model_at_most
#print axioms hasGlobalModelAtMost_implies_typed_hasGlobalModelAtMost
#print axioms no_published_global_model_at_most_of_no_typed_global_model_at_most

end

end D5.S1.Digit.PublishedGoldenBase4Problem
