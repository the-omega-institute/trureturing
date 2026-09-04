/- GID: D5/S0/Automata/PrefixColoringSoundness
   generality: G
   mirror-B: D5/B/S0/Automata/PrefixColoringSoundness
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Every DFAO compatible with a labeled prefix graph induces a transition- and output-consistent state coloring. -/

import D5.S0.Automata.DFAOStateLowerBound

/- Library-search audit trail (2026-09-01):
   * The frozen DFAO node supplies Mathlib DFA evaluation and append semantics.
   * The published DFA-identification pipeline uses an augmented prefix tree
     acceptor and graph coloring. No repository node stated the proof-relevant
     direction from a fitting DFAO to a consistent prefix coloring.
   * This direction is the soundness half required for lower bounds: if a
     finite prefix graph has no coloring by a proposed state carrier, then no
     DFAO on that carrier fits the labeled sample. The converse construction
     and the CNF equivalence remain separate nodes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.PrefixColoringSoundness

open D5.S0.Automata.DFAOStateLowerBound

universe u v w z

/-- A proof-relevant labeled prefix graph. `child_word` records that every edge
really appends the displayed symbol. -/
structure PrefixGraph (Alphabet : Type u) (Output : Type v) (Node : Type w) where
  word : Node → List Alphabet
  child : Node → Alphabet → Option Node
  child_word : ∀ ⦃node symbol next⦄,
    child node symbol = some next → word next = word node ++ [symbol]
  terminalOutput : Node → Option Output

/-- A DFAO is compatible with every terminal label in the prefix graph. -/
def Compatible {Alphabet : Type u} {Output : Type v}
    {Node : Type w} {State : Type z}
    (machine : DFAO Alphabet Output State)
    (graph : PrefixGraph Alphabet Output Node) : Prop :=
  ∀ ⦃node output⦄, graph.terminalOutput node = some output →
    machine.evalOutput (graph.word node) = output

/-- A coloring is deterministic along common labeled edges and never merges
terminal nodes with different outputs. -/
structure Coloring {Alphabet : Type u} {Output : Type v}
    {Node : Type w} (graph : PrefixGraph Alphabet Output Node)
    (Color : Type z) where
  color : Node → Color
  transition_consistent : ∀ ⦃left right symbol leftNext rightNext⦄,
    color left = color right →
    graph.child left symbol = some leftNext →
    graph.child right symbol = some rightNext →
    color leftNext = color rightNext
  terminal_consistent : ∀ ⦃left right leftOutput rightOutput⦄,
    color left = color right →
    graph.terminalOutput left = some leftOutput →
    graph.terminalOutput right = some rightOutput →
    leftOutput = rightOutput

/-- A compatible DFAO colors every prefix node by the state reached after its
stored word. -/
def reachedStateColoring {Alphabet : Type u} {Output : Type v}
    {Node : Type w} {State : Type z}
    (machine : DFAO Alphabet Output State)
    (graph : PrefixGraph Alphabet Output Node)
    (compatible : Compatible machine graph) : Coloring graph State where
  color := fun node => machine.toDFA.eval (graph.word node)
  transition_consistent := by
    intro left right symbol leftNext rightNext sameColor leftEdge rightEdge
    change machine.toDFA.eval (graph.word leftNext) =
      machine.toDFA.eval (graph.word rightNext)
    rw [graph.child_word leftEdge, graph.child_word rightEdge]
    change
      machine.toDFA.evalFrom machine.toDFA.start
          (graph.word left ++ [symbol]) =
        machine.toDFA.evalFrom machine.toDFA.start
          (graph.word right ++ [symbol])
    rw [machine.toDFA.evalFrom_of_append,
      machine.toDFA.evalFrom_of_append]
    exact congrArg
      (fun state => machine.toDFA.evalFrom state [symbol]) sameColor
  terminal_consistent := by
    intro left right leftOutput rightOutput sameColor leftTerminal rightTerminal
    have leftCorrect := compatible leftTerminal
    have rightCorrect := compatible rightTerminal
    calc
      leftOutput = machine.evalOutput (graph.word left) := leftCorrect.symm
      _ = machine.evalOutput (graph.word right) := by
        unfold DFAO.evalOutput
        exact congrArg machine.output sameColor
      _ = rightOutput := rightCorrect

/-- Uncolorability by a fixed state carrier excludes every compatible DFAO on
that carrier. -/
theorem no_compatible_machine_of_no_coloring
    {Alphabet : Type u} {Output : Type v}
    {Node : Type w} {State : Type z}
    (graph : PrefixGraph Alphabet Output Node)
    (noColoring : ¬ Nonempty (Coloring graph State)) :
    ¬ ∃ machine : DFAO Alphabet Output State, Compatible machine graph := by
  rintro ⟨machine, compatible⟩
  exact noColoring ⟨reachedStateColoring machine graph compatible⟩

#print axioms reachedStateColoring
#print axioms no_compatible_machine_of_no_coloring

end D5.S0.Automata.PrefixColoringSoundness
