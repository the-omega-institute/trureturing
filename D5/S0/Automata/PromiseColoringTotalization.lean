/- GID: D5/S0/Automata/PromiseColoringTotalization
   generality: G
   mirror-B: D5/B/S0/Automata/PromiseColoringTotalization
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Computability.MyhillNerode]
   utility: none
   digest: Transition-consistent conflict colorings of arbitrary nonempty promise domains characterize complete output automata with the same state budget. -/

import D5.S0.Automata.FiniteSampleRestriction
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.PromiseColoringTotalization

open D5.S0.Automata.DFAOStateLowerBound
open D5.S0.Automata.FiniteSampleRestriction

universe u v w

variable {Alphabet : Type u} {Output : Type v}

/-- All prefixes of legal words, with no finiteness condition on the domain. -/
def Prefixes (D : Set (List Alphabet)) : Set (List Alphabet) :=
  {word | ∃ suffix, word ++ suffix ∈ D}

/-- Distinct prefixes conflict exactly when a common legal continuation has
unequal prescribed outputs. Words outside `D` have no prescribed output. -/
def Conflict (D : Set (List Alphabet)) (f : D → Output)
    (left right : Prefixes D) : Prop :=
  left ≠ right ∧ ∃ (suffix : List Alphabet)
    (hl : left.val ++ suffix ∈ D) (hr : right.val ++ suffix ∈ D),
    f ⟨left.val ++ suffix, hl⟩ ≠ f ⟨right.val ++ suffix, hr⟩

/-- Only colors and the two source laws are supplied; no transition table,
output table, or already-realized prefix runs are part of the input. -/
structure Coloring (D : Set (List Alphabet)) (f : D → Output)
    (Color : Type w) where
  color : Prefixes D → Color
  proper : ∀ left right, Conflict D f left right → color left ≠ color right
  consistent : ∀ (left right : Prefixes D) (symbol : Alphabet)
    (hl : left.val ++ [symbol] ∈ Prefixes D)
    (hr : right.val ++ [symbol] ∈ Prefixes D),
    color left = color right →
      color ⟨left.val ++ [symbol], hl⟩ = color ⟨right.val ++ [symbol], hr⟩

private def terminal {D : Set (List Alphabet)} (word : D) : Prefixes D :=
  ⟨word.val, ⟨[], by simpa only [List.append_nil] using word.property⟩⟩

private def root {D : Set (List Alphabet)} (seed : D) : Prefixes D :=
  ⟨[], ⟨seed.val, by simpa only [List.nil_append] using seed.property⟩⟩

private theorem terminal_eq {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (left right : D)
    (same : c.color (terminal left) = c.color (terminal right)) :
    f left = f right := by
  by_contra different
  have distinct : terminal left ≠ terminal right := by
    intro equal
    apply different
    exact congrArg f (Subtype.ext (congrArg (fun p : Prefixes D => p.val) equal))
  apply c.proper (terminal left) (terminal right) ?_ same
  refine ⟨distinct, [], ?_, ?_, ?_⟩
  · simpa only [terminal, List.append_nil] using left.property
  · simpa only [terminal, List.append_nil] using right.property
  · simpa only [terminal, List.append_nil] using different

/-- Choose an observed successor when one exists; otherwise use the root color.
Classical choice does not assert that the coloring is computable. -/
noncomputable def completedStep {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed : D)
    (state : Color) (symbol : Alphabet) : Color := by
  classical
  exact if h : ∃ p : Prefixes D,
      c.color p = state ∧ p.val ++ [symbol] ∈ Prefixes D then
    c.color ⟨(Classical.choose h).val ++ [symbol], (Classical.choose_spec h).2⟩
  else c.color (root seed)

/-- Choose a prescribed output in the color class if present. A legal seed
supplies the default output, without a separate inhabitance assumption on Y. -/
noncomputable def completedOutput {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed : D) (state : Color) : Output := by
  classical
  exact if h : ∃ word : D, c.color (terminal word) = state then
    f (Classical.choose h)
  else f seed

/-- A complete total output automaton on exactly the supplied color carrier. -/
noncomputable def complete {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed : D) :
    DFAO Alphabet Output Color where
  start := c.color (root seed)
  step := completedStep c seed
  accept := ∅
  output := completedOutput c seed

private theorem completedStep_eq {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed : D)
    (p : Prefixes D) (symbol : Alphabet)
    (hp : p.val ++ [symbol] ∈ Prefixes D) :
    completedStep c seed (c.color p) symbol = c.color ⟨p.val ++ [symbol], hp⟩ := by
  classical
  have existsSource : ∃ q : Prefixes D,
      c.color q = c.color p ∧ q.val ++ [symbol] ∈ Prefixes D := ⟨p, rfl, hp⟩
  simp only [completedStep, dif_pos existsSource]
  exact c.consistent (Classical.choose existsSource) p symbol
    (Classical.choose_spec existsSource).2 hp (Classical.choose_spec existsSource).1

private theorem completedOutput_eq {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed word : D) :
    completedOutput c seed (c.color (terminal word)) = f word := by
  classical
  have existsLabel : ∃ q : D,
      c.color (terminal q) = c.color (terminal word) := ⟨word, rfl⟩
  simp only [completedOutput, dif_pos existsLabel]
  exact terminal_eq c (Classical.choose existsLabel) word
    (Classical.choose_spec existsLabel)

private theorem complete_reaches {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed : D)
    (word : List Alphabet) (legal : word ∈ Prefixes D) :
    (complete c seed).toDFA.eval word = c.color ⟨word, legal⟩ := by
  revert legal
  induction word using List.reverseRecOn with
  | nil => intro legal; rfl
  | append_singleton word symbol ih =>
      intro legal
      have parent : word ∈ Prefixes D := by
        obtain ⟨suffix, hs⟩ := legal
        exact ⟨[symbol] ++ suffix, by simpa only [List.append_assoc] using hs⟩
      rw [DFA.eval_append_singleton, ih parent]
      exact completedStep_eq c seed ⟨word, parent⟩ symbol legal

private theorem complete_correct {D : Set (List Alphabet)} {f : D → Output}
    {Color : Type w} (c : Coloring D f Color) (seed : D) :
    CorrectOnFamily (complete c seed) Subtype.val f := by
  intro word
  unfold DFAO.evalOutput
  rw [complete_reaches c seed word.val (terminal word).property]
  exact completedOutput_eq c seed word

/-- Actual reached states give the promised coloring for every complete machine. -/
def reachedColoring {D : Set (List Alphabet)} {f : D → Output}
    {State : Type w} (machine : DFAO Alphabet Output State)
    (correct : CorrectOnFamily machine Subtype.val f) : Coloring D f State where
  color p := machine.toDFA.eval p.val
  proper := by
    rintro left right ⟨_, suffix, hl, hr, different⟩ same
    apply different
    calc
      f ⟨left.val ++ suffix, hl⟩ = machine.evalOutput (left.val ++ suffix) :=
        (correct ⟨left.val ++ suffix, hl⟩).symm
      _ = machine.evalOutput (right.val ++ suffix) := by
        unfold DFAO.evalOutput
        change machine.output (machine.toDFA.evalFrom machine.start (left.val ++ suffix)) =
          machine.output (machine.toDFA.evalFrom machine.start (right.val ++ suffix))
        rw [DFA.evalFrom_of_append, DFA.evalFrom_of_append]
        exact congrArg (fun q => machine.output (machine.toDFA.evalFrom q suffix)) same
      _ = f ⟨right.val ++ suffix, hr⟩ := correct ⟨right.val ++ suffix, hr⟩
  consistent := by
    intro left right symbol hl hr same
    change machine.toDFA.eval (left.val ++ [symbol]) =
      machine.toDFA.eval (right.val ++ [symbol])
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton]
    exact congrArg (fun q => machine.step q symbol) same

/- This consumed capacity argument extracts the explicit embedding/retraction
already used locally by BoundedStateSampleCompactness. It is not claimed as
new mathematics and cannot be imported from that theorem's local `pad`. -/
private theorem exists_capacity_machine {State : Type w} [Fintype State]
    (machine : DFAO Alphabet Output State) (s : ℕ) (bound : Fintype.card State ≤ s) :
    ∃ padded : DFAO Alphabet Output (Fin s),
      ∀ word, padded.evalOutput word = machine.evalOutput word := by
  classical
  let embed : State → Fin s := fun q => (Fintype.equivFin State q).castLE bound
  have injective : Function.Injective embed := by
    intro p q equal
    apply (Fintype.equivFin State).injective
    exact Fin.ext (congrArg (fun x : Fin s => x.val) equal)
  letI : Nonempty State := ⟨machine.start⟩
  let retract : Fin s → State := Function.invFun embed
  have retract_embed : ∀ q, retract (embed q) = q :=
    Function.leftInverse_invFun injective
  let padded : DFAO Alphabet Output (Fin s) :=
    { start := embed machine.start
      step := fun q a => embed (machine.step (retract q) a)
      accept := ∅
      output := fun q => machine.output (retract q) }
  have run : ∀ (word : List Alphabet) (q : State),
      padded.toDFA.evalFrom (embed q) word = embed (machine.toDFA.evalFrom q word) := by
    intro word
    induction word with
    | nil => intro q; rfl
    | cons a tail ih =>
        intro q
        simp only [DFA.evalFrom_cons]
        change padded.toDFA.evalFrom
          (embed (machine.step (retract (embed q)) a)) tail = _
        rw [retract_embed, ih]
  refine ⟨padded, ?_⟩
  intro word
  change machine.output (retract (padded.toDFA.evalFrom (embed machine.start) word)) = _
  rw [run, retract_embed]
  rfl

/-- Exact state-budget characterization for arbitrary nonempty promise domains.
Neither alphabet nor output type nor promise domain is assumed finite. -/
theorem promise_coloring_iff_total_dfao
    (D : Set (List Alphabet)) (f : D → Output) (nonempty : D.Nonempty)
    (s : ℕ) (_positive : 0 < s) :
    (∃ (State : Type w) (_ : Fintype State) (machine : DFAO Alphabet Output State),
      Fintype.card State ≤ s ∧ CorrectOnFamily machine Subtype.val f) ↔
    Nonempty (Coloring D f (Fin s)) := by
  classical
  constructor
  · rintro ⟨State, inst, machine, bound, correct⟩
    obtain ⟨padded, agrees⟩ := exists_capacity_machine machine s bound
    exact ⟨reachedColoring padded (fun word => (agrees word.val).trans (correct word))⟩
  · rintro ⟨c⟩
    obtain ⟨word, legal⟩ := nonempty
    let seed : D := ⟨word, legal⟩
    let e : Fin s ≃ ULift.{w} (Fin s) := Equiv.ulift.symm
    let machine : DFAO Alphabet Output (ULift.{w} (Fin s)) :=
      { toDFA := DFA.reindex e (complete c seed).toDFA
        output := fun q => (complete c seed).output (e.symm q) }
    refine ⟨ULift.{w} (Fin s), inferInstance, machine, by simp, ?_⟩
    intro input
    change (complete c seed).output
      (e.symm ((DFA.reindex e (complete c seed).toDFA).eval input.val)) = f input
    rw [DFA.eval_reindex, e.symm_apply_apply]
    exact complete_correct c seed input

#print axioms promise_coloring_iff_total_dfao

end D5.S0.Automata.PromiseColoringTotalization
