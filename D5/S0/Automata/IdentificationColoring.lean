/- GID: D5/S0/Automata/IdentificationColoring
   generality: G
   mirror-B: D5/B/S0/Automata/IdentificationColoring
   mirror-E: none(waiver:proof-carrying-identification)
   anchors: []
   digest: A valid prefix-tree coloring is equivalent to a typed partial DFAO together with certified reached states on every sample prefix. -/

import D5.S0.Automata.LabeledPrefixTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.IdentificationColoring

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.LabeledPrefixTree

universe u v w x

/-- A finite identification coloring packages the transition table together
with a proof that every prefix occurrence reaches its declared color. -/
structure Identification
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) where
  color : PrefixNode sample → Color
  start : Color
  stateType : Color → BaseState
  transition : Color → Alphabet → Option Color
  output : Color → Output
  start_type : stateType start = base.start
  transition_type :
    ∀ ⦃state symbol next⦄,
      transition state symbol = some next →
        base.step (stateType state) symbol = some (stateType next)
  prefix_run :
    ∀ node,
      runTransition transition start (prefixWord sample node) =
        some (color node)
  output_sound :
    ∀ index,
      output (color (leafOccurrence sample index)) =
        sample.label index

namespace Identification

/-- Equal prefix words necessarily receive the same color. -/
theorem color_eq_of_samePrefix
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color)
    {left right : PrefixNode sample}
    (same : SamePrefix sample left right) :
    identification.color left = identification.color right := by
  apply Option.some.inj
  calc
    some (identification.color left) =
        runTransition identification.transition identification.start
          (prefixWord sample left) :=
      (identification.prefix_run left).symm
    _ = runTransition identification.transition identification.start
          (prefixWord sample right) := by
      rw [same]
    _ = some (identification.color right) :=
      identification.prefix_run right

/-- The partial DFAO represented by an identification coloring. -/
def toMachine
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color) :
    TypedPartialDFAO base Output Color where
  start := identification.start
  stateType := identification.stateType
  step := identification.transition
  output := identification.output
  start_type := identification.start_type
  step_type := identification.transition_type

end Identification

/-- A typed partial DFAO fits every word and output in a finite labeled sample. -/
def FitsSample
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    {base : PartialDFA Alphabet BaseState}
    {State : Type x}
    (machine : TypedPartialDFAO base Output State) : Prop :=
  ∀ index,
    machine.evalOutput (sample.word index) = some (sample.label index)

/-- A realization chooses the actual reached state of a typed machine at every
prefix occurrence. -/
structure PrefixRealization
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    {base : PartialDFA Alphabet BaseState}
    {State : Type x}
    (machine : TypedPartialDFAO base Output State) where
  stateAt : PrefixNode sample → State
  run_stateAt :
    ∀ node,
      machine.run (prefixWord sample node) = some (stateAt node)

/-- A valid identification coloring produces a machine that fits its sample. -/
theorem Identification.toMachine_fitsSample
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color) :
    FitsSample sample identification.toMachine := by
  intro index
  unfold TypedPartialDFAO.evalOutput TypedPartialDFAO.run
    TypedPartialDFAO.runFrom Identification.toMachine
  rw [← prefixWord_leafOccurrence sample index]
  rw [identification.prefix_run]
  simp [identification.output_sound index]

/-- The colors of an identification form a prefix realization of its induced
machine. -/
def Identification.toPrefixRealization
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color) :
    PrefixRealization sample identification.toMachine where
  stateAt := identification.color
  run_stateAt := identification.prefix_run

/-- A machine, its reached-state realization, and finite-sample correctness
reconstruct a valid identification coloring. -/
def Identification.ofMachine
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {State : Type x}
    (machine : TypedPartialDFAO base Output State)
    (realization : PrefixRealization sample machine)
    (fits : FitsSample sample machine) :
    Identification sample base State where
  color := realization.stateAt
  start := machine.start
  stateType := machine.stateType
  transition := machine.step
  output := machine.output
  start_type := machine.start_type
  transition_type := machine.step_type
  prefix_run := realization.run_stateAt
  output_sound := by
    intro index
    have hfit := fits index
    unfold TypedPartialDFAO.evalOutput at hfit
    rw [← prefixWord_leafOccurrence sample index] at hfit
    rw [realization.run_stateAt] at hfit
    simpa using hfit

/-- Identification colorings are exactly typed partial machines equipped with
certified reached states on all sample prefixes and correct terminal outputs. -/
theorem identification_iff_machine_realization
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) :
    Nonempty (Identification sample base Color) ↔
      ∃ machine : TypedPartialDFAO base Output Color,
        Nonempty (PrefixRealization sample machine) ∧
          FitsSample sample machine := by
  constructor
  · rintro ⟨identification⟩
    exact ⟨identification.toMachine,
      ⟨identification.toPrefixRealization⟩,
      identification.toMachine_fitsSample⟩
  · rintro ⟨machine, ⟨realization⟩, fits⟩
    exact ⟨Identification.ofMachine machine realization fits⟩

#print axioms Identification.color_eq_of_samePrefix
#print axioms identification_iff_machine_realization

end D5.S0.Automata.IdentificationColoring
