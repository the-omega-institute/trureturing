/- GID: D5/S0/Automata/LabeledPrefixTree
   generality: G
   mirror-B: D5/B/S0/Automata/LabeledPrefixTree
   mirror-E: none(waiver:finite-sample-prefix-carrier)
   anchors: []
   digest: Finite labeled samples carry a canonical finite family of prefix occurrences with exact leaf and extension semantics. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.LabeledPrefixTree

universe u v w

/-- A finite family of labeled words. The index type is bundled so later
certificate formats can quantify over one self-contained sample object. -/
structure LabeledSample (Alphabet : Type u) (Output : Type v) where
  Index : Type w
  indexFintype : Fintype Index
  word : Index → List Alphabet
  label : Index → Output

attribute [instance] LabeledSample.indexFintype

/-- The occurrence of a prefix is a sample index together with a cut position.
Equal words occurring in different samples remain separate nodes; later
identification colorings are required to identify equal prefix words. -/
abbrev PrefixNode {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output) :=
  Σ index : sample.Index, Fin ((sample.word index).length + 1)

/-- The word represented by a prefix occurrence. -/
def prefixWord {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (node : PrefixNode sample) : List Alphabet :=
  (sample.word node.1).take node.2.val

/-- The zero-length prefix occurrence attached to one sample word. -/
def rootOccurrence {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (index : sample.Index) : PrefixNode sample :=
  ⟨index, ⟨0, Nat.zero_lt_succ _⟩⟩

/-- The full-word leaf occurrence attached to one sample word. -/
def leafOccurrence {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (index : sample.Index) : PrefixNode sample :=
  ⟨index, ⟨(sample.word index).length, Nat.lt_succ_self _⟩⟩

@[simp]
theorem prefixWord_rootOccurrence
    {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (index : sample.Index) :
    prefixWord sample (rootOccurrence sample index) = [] := by
  simp [prefixWord, rootOccurrence]

@[simp]
theorem prefixWord_leafOccurrence
    {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (index : sample.Index) :
    prefixWord sample (leafOccurrence sample index) =
      sample.word index := by
  simp [prefixWord, leafOccurrence]

/-- Two occurrences denote the same trie node exactly when their prefix words
are equal. -/
def SamePrefix {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (left right : PrefixNode sample) : Prop :=
  prefixWord sample left = prefixWord sample right

/-- One occurrence extends another by one symbol. -/
def ExtendsBy {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (parent : PrefixNode sample) (symbol : Alphabet)
    (child : PrefixNode sample) : Prop :=
  prefixWord sample child = prefixWord sample parent ++ [symbol]

/-- A terminal occurrence carries the sample label of its full word. -/
def TerminalLabel {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (node : PrefixNode sample) (output : Output) : Prop :=
  ∃ index,
    SamePrefix sample node (leafOccurrence sample index) ∧
      output = sample.label index

/-- Every canonical prefix occurrence is genuinely a prefix of its source
sample word. -/
theorem prefixWord_isPrefix
    {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output)
    (node : PrefixNode sample) :
    prefixWord sample node <+: sample.word node.1 := by
  exact List.take_prefix _ _

/-- The canonical prefix occurrence family is finite whenever the sample index
family is finite. -/
noncomputable instance prefixNodeFintype
    {Alphabet : Type u} {Output : Type v}
    (sample : LabeledSample Alphabet Output) :
    Fintype (PrefixNode sample) := by
  haveI := sample.indexFintype
  haveI : DecidableEq sample.Index := Classical.decEq _
  unfold PrefixNode
  infer_instance

/-- Restrict a sparse problem to its first `extent` labeled addresses. -/
def prefixSample
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem :
      D5.S0.Automata.TypedPartialDFAOOverBase.SparseProblem
        Alphabet Output BaseState)
    (extent : Nat) : LabeledSample Alphabet Output where
  Index := Fin extent
  indexFintype := inferInstance
  word index := problem.input index.val
  label index := problem.target index.val

/-- The leaves of a finite sparse-problem sample recover exactly the selected
input words. -/
theorem prefixSample_leaf_word
    {Alphabet : Type u} {Output : Type v} {BaseState : Type w}
    (problem :
      D5.S0.Automata.TypedPartialDFAOOverBase.SparseProblem
        Alphabet Output BaseState)
    (extent : Nat) (index : Fin extent) :
    prefixWord (prefixSample problem extent)
      (leafOccurrence (prefixSample problem extent) index) =
        problem.input index.val := by
  simp [prefixSample]

#print axioms prefixWord_isPrefix
#print axioms prefixSample_leaf_word

end D5.S0.Automata.LabeledPrefixTree
