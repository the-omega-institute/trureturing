/- GID: D5/S0/Automata/ZeroAnchoredSparseDFAO
   generality: G
   mirror-B: D5/B/S0/Automata/ZeroAnchoredSparseDFAO
   mirror-E: none(waiver:zero-anchored-sparse-machine-semantics)
   anchors: [D5/S0/Automata/TypedPartialDFAO]
   digest: A zero-anchored sparse problem fixes the base automaton, leading-zero symbol, zero output, and sparse target sequence for an exact typed partial DFAO. -/

import D5.S0.Automata.TypedPartialDFAO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.ZeroAnchoredSparseDFAO

open D5.S0.Automata.TypedPartialDFAO

universe u v w x

/-- A sparse output problem with the extra data used by a published
leading-zero-invariant DFAO model: the base validity automaton, the leading-zero
symbol, and the output required on the zero word. -/
structure Problem (Alphabet : Type u) (Output : Type v)
    (BaseState : Type w) where
  base : BaseAutomaton Alphabet BaseState
  zero : Alphabet
  zeroOutput : Output
  input : Nat → List Alphabet
  target : Nat → Output

namespace Problem

/-- The machine uses exactly the base automaton and leading-zero symbol fixed by
the problem. -/
def MachineMatches
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    {State : Type x}
    (machine : Machine Alphabet Output BaseState State) : Prop :=
  machine.base = problem.base ∧ machine.zero = problem.zero

/-- The machine gives the declared output on the one-symbol zero word. The
machine structure already requires that this symbol loops at the start state. -/
def HasZeroAnchor
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    {State : Type x}
    (machine : Machine Alphabet Output BaseState State) : Prop :=
  machine.evalOutput [problem.zero] = some problem.zeroOutput

/-- Global correctness in the zero-anchored sparse model class. -/
def Correct
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    {State : Type x}
    (machine : Machine Alphabet Output BaseState State) : Prop :=
  problem.MachineMatches machine ∧
    problem.HasZeroAnchor machine ∧
      ∀ index, machine.evalOutput (problem.input index) =
        some (problem.target index)

/-- Correctness on the zero anchor and the first `extent` sparse addresses. -/
def FitsPrefix
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (extent : Nat)
    {State : Type x}
    (machine : Machine Alphabet Output BaseState State) : Prop :=
  problem.MachineMatches machine ∧
    problem.HasZeroAnchor machine ∧
      ∀ index, index < extent →
        machine.evalOutput (problem.input index) =
          some (problem.target index)

/-- The one-symbol zero anchor is equivalent to reading the output of the start
state once the machine and problem zero symbols agree. -/
theorem hasZeroAnchor_iff_start_output
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    {State : Type x}
    (machine : Machine Alphabet Output BaseState State)
    (zeroMatches : machine.zero = problem.zero) :
    problem.HasZeroAnchor machine ↔
      machine.output machine.start = problem.zeroOutput := by
  unfold HasZeroAnchor
  rw [← zeroMatches]
  simp [Machine.evalOutput, Machine.run, Machine.runFrom,
    machine.start_zero_loop]

/-- Global correctness implies every finite-prefix fitting obligation in the
same model class. -/
theorem correct_implies_fitsPrefix
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    {State : Type x}
    (machine : Machine Alphabet Output BaseState State)
    (correct : problem.Correct machine)
    (extent : Nat) : problem.FitsPrefix extent machine := by
  rcases correct with ⟨matches, anchor, sparse⟩
  exact ⟨matches, anchor, fun index _ => sparse index⟩

/-- Existence of a globally correct zero-anchored machine with exactly the
named finite state type. -/
def HasGlobalModel
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (states : Nat) : Prop :=
  ∃ machine : Machine Alphabet Output BaseState (Fin states),
    problem.Correct machine

/-- Existence of a globally correct zero-anchored machine using at most the
selected state budget. -/
def HasGlobalModelAtMost
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (bound : Nat) : Prop :=
  ∃ states, states ≤ bound ∧ problem.HasGlobalModel states

/-- Existence of a zero-anchored finite-prefix model using at most the selected
state budget. -/
def HasPrefixModelAtMost
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    (extent bound : Nat) : Prop :=
  ∃ states, states ≤ bound ∧
    ∃ machine : Machine Alphabet Output BaseState (Fin states),
      problem.FitsPrefix extent machine

/-- Every globally correct bounded-state model induces a model of every finite
prefix while preserving the fixed base, zero loop, and zero output anchor. -/
theorem global_model_at_most_implies_prefix_model_at_most
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem : Problem Alphabet Output BaseState)
    {extent bound : Nat} :
    problem.HasGlobalModelAtMost bound →
      problem.HasPrefixModelAtMost extent bound := by
  rintro ⟨states, hstates, machine, correct⟩
  exact ⟨states, hstates, machine,
    problem.correct_implies_fitsPrefix machine correct extent⟩

#print axioms hasZeroAnchor_iff_start_output
#print axioms correct_implies_fitsPrefix
#print axioms global_model_at_most_implies_prefix_model_at_most

end Problem

end D5.S0.Automata.ZeroAnchoredSparseDFAO
