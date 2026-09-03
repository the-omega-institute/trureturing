/- GID: D5/S0/Automata/TypedStableRightCongruence
   generality: G
   mirror-B: D5/B/S0/Automata/TypedStableRightCongruence
   mirror-E: none(waiver:typed-prefix-congruence-semantics)
   anchors: [D5/S0/Automata/PrefixColoringSoundness]
   digest: A typed stable right congruence is the transition-stable finite partition forced on a labeled prefix family by every typed partial DFAO realization. -/

import D5.S0.Automata.IdentificationColoring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TypedStableRightCongruence

open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Automata.LabeledPrefixTree
open D5.S0.Automata.IdentificationColoring

universe u v w x

/-- The quotient data visible on a finite labeled prefix family. It remembers
which occurrences share a state, certifies the base-automaton type of every
color, forces right stability on every pair of observed equal-color edges, and
prevents two equal-color leaves from carrying different outputs. -/
structure StableRightCongruence
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x) where
  color : PrefixNode sample → Color
  stateType : Color → BaseState
  samePrefix :
    ∀ ⦃left right : PrefixNode sample⦄,
      SamePrefix sample left right → color left = color right
  base_run :
    ∀ node,
      base.eval (prefixWord sample node) =
        some (stateType (color node))
  right_stable :
    ∀ ⦃leftParent rightParent leftChild rightChild : PrefixNode sample⦄
      ⦃symbol : Alphabet⦄,
      color leftParent = color rightParent →
        ExtendsBy sample leftParent symbol leftChild →
          ExtendsBy sample rightParent symbol rightChild →
            color leftChild = color rightChild
  terminal_stable :
    ∀ left right,
      color (leafOccurrence sample left) =
          color (leafOccurrence sample right) →
        sample.label left = sample.label right

/-- Every observed one-symbol extension exposes the corresponding entry of the
shared transition table of an identification coloring. -/
theorem identification_transition_of_extendsBy
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color)
    {parent child : PrefixNode sample} {symbol : Alphabet}
    (edge : ExtendsBy sample parent symbol child) :
    identification.transition (identification.color parent) symbol =
      some (identification.color child) := by
  have childRun := identification.prefix_run child
  rw [edge] at childRun
  change identification.toMachine.runFrom identification.toMachine.start
      (prefixWord sample parent ++ [symbol]) =
        some (identification.color child) at childRun
  rw [TypedPartialDFAO.runFrom_append] at childRun
  have parentRun := identification.prefix_run parent
  change identification.toMachine.runFrom identification.toMachine.start
      (prefixWord sample parent) =
        some (identification.color parent) at parentRun
  rw [parentRun] at childRun
  simpa [TypedPartialDFAO.runFrom, runTransition,
    Identification.toMachine] using childRun

/-- Every valid identification coloring induces its explicit typed stable right
congruence. This forgetful map is the semantic target needed by quotient-first
and branch-atlas refutation encodings. -/
def identificationToStableRightCongruence
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    {sample : LabeledSample Alphabet Output}
    {base : PartialDFA Alphabet BaseState}
    {Color : Type x}
    (identification : Identification sample base Color) :
    StableRightCongruence sample base Color where
  color := identification.color
  stateType := identification.stateType
  samePrefix := identification.color_eq_of_samePrefix
  base_run := by
    intro node
    have projected :=
      TypedPartialDFAO.runFrom_type identification.toMachine
        (identification.prefix_run node)
    simpa [PartialDFA.eval, Identification.toMachine,
      identification.start_type] using projected
  right_stable := by
    intro leftParent rightParent leftChild rightChild symbol
      sameParent leftEdge rightEdge
    apply Option.some.inj
    calc
      some (identification.color leftChild) =
          identification.transition
            (identification.color leftParent) symbol :=
        (identification_transition_of_extendsBy identification leftEdge).symm
      _ = identification.transition
            (identification.color rightParent) symbol := by
        rw [sameParent]
      _ = some (identification.color rightChild) :=
        identification_transition_of_extendsBy identification rightEdge
  terminal_stable := by
    intro left right sameLeaf
    calc
      sample.label left =
          identification.output
            (identification.color (leafOccurrence sample left)) :=
        (identification.output_sound left).symm
      _ = identification.output
            (identification.color (leafOccurrence sample right)) := by
        rw [sameLeaf]
      _ = sample.label right := identification.output_sound right

/-- Refuting every stable right congruence on a color type refutes every full
identification using that color type. -/
theorem no_identification_of_no_stableRightCongruence
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (sample : LabeledSample Alphabet Output)
    (base : PartialDFA Alphabet BaseState)
    (Color : Type x)
    (none : ¬Nonempty (StableRightCongruence sample base Color)) :
    ¬Nonempty (Identification sample base Color) := by
  rintro ⟨identification⟩
  exact none ⟨identificationToStableRightCongruence identification⟩

#print axioms identification_transition_of_extendsBy
#print axioms identificationToStableRightCongruence
#print axioms no_identification_of_no_stableRightCongruence

end D5.S0.Automata.TypedStableRightCongruence
