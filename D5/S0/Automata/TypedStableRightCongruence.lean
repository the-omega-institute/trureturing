/- GID: D5/S0/Automata/TypedStableRightCongruence
   generality: G
   mirror-B: D5/B/S0/Automata/TypedStableRightCongruence
   mirror-E: none(waiver:finite-sample-right-congruence)
   anchors: []
   digest: Every finite typed DFAO identification induces a typed stable right coloring of prefix occurrences, so refuting the weaker coloring already refutes every machine. -/

import D5.S0.Automata.IdentificationColoring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TypedStableRightCongruence

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.LabeledPrefixTree
open D5.S0.Automata.IdentificationColoring

universe u v w x

/-- A finite-color right-congruence relaxation of typed DFAO identification.
It remembers exactly the local conditions forced on prefix states by any
deterministic typed machine, while omitting an explicit transition table. -/
structure TypedStableRightColoring
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) where
  color : PrefixNode sample → Color
  root : Color
  root_color :
    ∀ index, color (rootOccurrence sample index) = root
  samePrefix_color :
    ∀ ⦃left right⦄,
      SamePrefix sample left right → color left = color right
  right_stable :
    ∀ ⦃leftParent rightParent symbol leftChild rightChild⦄,
      ExtendsBy sample leftParent symbol leftChild →
      ExtendsBy sample rightParent symbol rightChild →
      color leftParent = color rightParent →
      color leftChild = color rightChild
  terminal_stable :
    ∀ leftIndex rightIndex,
      color (leafOccurrence sample leftIndex) =
          color (leafOccurrence sample rightIndex) →
        sample.label leftIndex = sample.label rightIndex
  base_compatible :
    ∀ ⦃left right⦄,
      color left = color right →
        base.eval (prefixWord sample left) =
          base.eval (prefixWord sample right)

namespace TypedStableRightColoring

private theorem transition_of_edge
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color)
    {parent child : PrefixNode sample} {symbol : Alphabet}
    (edge : ExtendsBy sample parent symbol child) :
    identification.transition (identification.color parent) symbol =
      some (identification.color child) := by
  have appendRun :=
    TypedPartialDFAO.runFrom_append identification.toMachine
      identification.start (prefixWord sample parent) [symbol]
  have appendRun' :
      runTransition identification.transition identification.start
          (prefixWord sample parent ++ [symbol]) =
        (runTransition identification.transition identification.start
          (prefixWord sample parent)).bind
            (fun reached =>
              runTransition identification.transition reached [symbol]) := by
    simpa [Identification.toMachine, TypedPartialDFAO.runFrom] using appendRun
  rw [← edge, identification.prefix_run child,
    identification.prefix_run parent] at appendRun'
  simpa [runTransition] using appendRun'.symm

/-- Every exact identification induces the weaker stable right coloring used by
structural and CNF lower-bound searches. -/
def ofIdentification
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color) :
    TypedStableRightColoring sample base Color where
  color := identification.color
  root := identification.start
  root_color := by
    intro index
    apply Option.some.inj
    have run := identification.prefix_run (rootOccurrence sample index)
    simpa [prefixWord_rootOccurrence, runTransition] using run.symm
  samePrefix_color := by
    intro left right same
    exact identification.color_eq_of_samePrefix same
  right_stable := by
    intro leftParent rightParent symbol leftChild rightChild
      leftEdge rightEdge sameParent
    have leftStep := transition_of_edge identification leftEdge
    have rightStep := transition_of_edge identification rightEdge
    apply Option.some.inj
    calc
      some (identification.color leftChild) =
          identification.transition
            (identification.color leftParent) symbol := leftStep.symm
      _ = identification.transition
            (identification.color rightParent) symbol := by
          rw [sameParent]
      _ = some (identification.color rightChild) := rightStep
  terminal_stable := by
    intro leftIndex rightIndex sameColor
    calc
      sample.label leftIndex =
          identification.output
            (identification.color
              (leafOccurrence sample leftIndex)) :=
        (identification.output_sound leftIndex).symm
      _ = identification.output
            (identification.color
              (leafOccurrence sample rightIndex)) := by
        rw [sameColor]
      _ = sample.label rightIndex :=
        identification.output_sound rightIndex
  base_compatible := by
    intro left right sameColor
    have leftRun :
        identification.toMachine.runFrom identification.start
            (prefixWord sample left) =
          some (identification.color left) := by
      simpa [Identification.toMachine, TypedPartialDFAO.runFrom] using
        identification.prefix_run left
    have rightRun :
        identification.toMachine.runFrom identification.start
            (prefixWord sample right) =
          some (identification.color right) := by
      simpa [Identification.toMachine, TypedPartialDFAO.runFrom] using
        identification.prefix_run right
    have leftType :=
      TypedPartialDFAO.runFrom_type identification.toMachine leftRun
    have rightType :=
      TypedPartialDFAO.runFrom_type identification.toMachine rightRun
    rw [identification.start_type] at leftType rightType
    calc
      base.eval (prefixWord sample left) =
          some (identification.stateType
            (identification.color left)) := by
        simpa [PartialDFA.eval] using leftType
      _ = some (identification.stateType
            (identification.color right)) := by
        rw [sameColor]
      _ = base.eval (prefixWord sample right) := by
        simpa [PartialDFA.eval] using rightType.symm

end TypedStableRightColoring

/-- Refuting the stable-right-coloring relaxation is sufficient to refute every
exact identification on the same finite color carrier. -/
theorem no_identification_of_no_stable_right_coloring
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (impossible :
      ¬Nonempty (TypedStableRightColoring sample base Color)) :
    ¬Nonempty (Identification sample base Color) := by
  rintro ⟨identification⟩
  exact impossible ⟨TypedStableRightColoring.ofIdentification identification⟩

/-- The same obstruction rules out a typed machine equipped with reached-state
realizations of all sample prefixes and correct terminal outputs. -/
theorem no_machine_realization_of_no_stable_right_coloring
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (impossible :
      ¬Nonempty (TypedStableRightColoring sample base Color)) :
    ¬(∃ machine : TypedPartialDFAO base Output Color,
        Nonempty (PrefixRealization sample machine) ∧
          FitsSample sample machine) := by
  intro witness
  have identification : Nonempty (Identification sample base Color) :=
    (identification_iff_machine_realization sample base Color).2 witness
  exact
    (no_identification_of_no_stable_right_coloring
      sample base Color impossible) identification

#print axioms TypedStableRightColoring.ofIdentification
#print axioms no_identification_of_no_stable_right_coloring
#print axioms no_machine_realization_of_no_stable_right_coloring

end D5.S0.Automata.TypedStableRightCongruence
