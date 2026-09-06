/- GID: D5/S0/Automata/ZeroInvariantTypedDFAO
   generality: G
   mirror-B: D5/B/S0/Automata/ZeroInvariantTypedDFAO
   mirror-E: none(waiver:published-automata-semantics)
   anchors: []
   digest: An anchored zero-invariant typed partial DFAO freezes the leading-zero convention and the distinguished zero output used by published sparse-automata experiments. -/

import D5.S0.Automata.TypedPartialDFAOOverBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.ZeroInvariantTypedDFAO

open D5.S0.Automata.TypedPartialDFAOOverBase

universe u v w x

/-- A typed partial DFAO together with the two semantic conditions used by the
published incomplete-data experiments: input zero fixes the start state, and
the start state carries a distinguished anchor output. -/
structure AnchoredZeroInvariantTypedDFAO
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    (base : PartialDFA Alphabet BaseState)
    (zero : Alphabet) (anchor : Output) (State : Type x) where
  toMachine : TypedPartialDFAO base Output State
  start_zero_loop :
    toMachine.step toMachine.start zero = some toMachine.start
  start_output :
    toMachine.output toMachine.start = anchor

namespace AnchoredZeroInvariantTypedDFAO

/-- Evaluate the underlying typed partial DFAO. -/
def evalOutput
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {base : PartialDFA Alphabet BaseState}
    {zero : Alphabet} {anchor : Output} {State : Type x}
    (machine : AnchoredZeroInvariantTypedDFAO base zero anchor State)
    (word : List Alphabet) : Option Output :=
  machine.toMachine.evalOutput word

/-- The empty word reads the distinguished anchor output. -/
@[simp] theorem evalOutput_nil
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {base : PartialDFA Alphabet BaseState}
    {zero : Alphabet} {anchor : Output} {State : Type x}
    (machine : AnchoredZeroInvariantTypedDFAO base zero anchor State) :
    machine.evalOutput [] = some anchor := by
  simp [evalOutput, TypedPartialDFAO.evalOutput, TypedPartialDFAO.run,
    TypedPartialDFAO.runFrom, runTransition, machine.start_output]

/-- A single leading zero also reads the distinguished anchor output. -/
@[simp] theorem evalOutput_singleton_zero
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {base : PartialDFA Alphabet BaseState}
    {zero : Alphabet} {anchor : Output} {State : Type x}
    (machine : AnchoredZeroInvariantTypedDFAO base zero anchor State) :
    machine.evalOutput [zero] = some anchor := by
  simp [evalOutput, TypedPartialDFAO.evalOutput, TypedPartialDFAO.run,
    TypedPartialDFAO.runFrom, runTransition, machine.start_zero_loop,
    machine.start_output]

/-- Any finite zero prefix is observationally invisible. -/
theorem evalOutput_replicate_zero
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {base : PartialDFA Alphabet BaseState}
    {zero : Alphabet} {anchor : Output} {State : Type x}
    (machine : AnchoredZeroInvariantTypedDFAO base zero anchor State)
    (count : Nat) (word : List Alphabet) :
    machine.evalOutput (List.replicate count zero ++ word) =
      machine.evalOutput word := by
  simpa [evalOutput] using
    TypedPartialDFAO.leading_zero_invariant
      machine.toMachine zero machine.start_zero_loop count word

/-- Forgetting the anchor and zero-loop evidence recovers the ordinary typed
partial DFAO used by the wider sparse-language problem. -/
def forget
    {Alphabet : Type u} {BaseState : Type v} {Output : Type w}
    {base : PartialDFA Alphabet BaseState}
    {zero : Alphabet} {anchor : Output} {State : Type x}
    (machine : AnchoredZeroInvariantTypedDFAO base zero anchor State) :
    TypedPartialDFAO base Output State :=
  machine.toMachine

#print axioms evalOutput_nil
#print axioms evalOutput_singleton_zero
#print axioms evalOutput_replicate_zero

end AnchoredZeroInvariantTypedDFAO

end D5.S0.Automata.ZeroInvariantTypedDFAO
