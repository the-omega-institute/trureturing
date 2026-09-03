/- GID: D5/S0/Automata/TypedBinaryReachabilityCardinality
   generality: G
   mirror-B: D5/B/S0/Automata/TypedBinaryReachabilityCardinality
   mirror-E: none(waiver:typed-reachability-cardinality)
   anchors: []
   digest: In a reachable binary Zeckendorf-typed partial DFAO, every previous-one state has a distinct previous-zero predecessor under input one, hence the previous-one fiber has no more states than the previous-zero fiber. -/

import D5.S0.Automata.TypedPartialDFAOOverBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Automata.TypedBinaryReachabilityCardinality

open D5.S0.Automata.TypedPartialDFAOOverBase

universe u v

/-- States whose numeration type records that the preceding input digit was zero. -/
abbrev PreviousZeroState
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State) :=
  { state : State // machine.stateType state = .previousZero }

/-- States whose numeration type records that the preceding input digit was one. -/
abbrev PreviousOneState
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State) :=
  { state : State // machine.stateType state = .previousOne }

/-- Reachability from the distinguished start state. -/
def Reachable
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    (state : State) : Prop :=
  ∃ word : List (Fin 2), machine.run word = some state

/-- Every named state is reached by some legal finite input word. -/
def AllStatesReachable
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State) : Prop :=
  ∀ state, Reachable machine state

/-- The exact image condition needed for the type-fiber cardinality bound. -/
def EveryOneStateHasOnePredecessor
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State) : Prop :=
  ∀ target : PreviousOneState machine,
    ∃ source : PreviousZeroState machine,
      machine.step source.1 (1 : Fin 2) = some target.1

private theorem run_append_singleton_eq_some
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    {wordPrefix : List (Fin 2)} {symbol : Fin 2} {target : State}
    (run : machine.run (wordPrefix ++ [symbol]) = some target) :
    ∃ source : State,
      machine.run wordPrefix = some source ∧
        machine.step source symbol = some target := by
  change machine.runFrom machine.start (wordPrefix ++ [symbol]) = some target at run
  rw [TypedPartialDFAO.runFrom_append] at run
  cases hprefix : machine.runFrom machine.start wordPrefix with
  | none =>
      simp [hprefix] at run
  | some source =>
      refine ⟨source, ?_, ?_⟩
      · exact hprefix
      · rw [hprefix] at run
        simp only [Option.bind_some] at run
        cases hstep : machine.step source symbol with
        | none =>
            simp [TypedPartialDFAO.runFrom, runTransition, hstep] at run
        | some next =>
            have hEq : some next = some target := by
              simpa [TypedPartialDFAO.runFrom, runTransition, hstep] using run
            exact hEq

private theorem step_to_previousOne_has_previousZero_source
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    {source target : State} {symbol : Fin 2}
    (step : machine.step source symbol = some target)
    (targetType : machine.stateType target = .previousOne) :
    machine.stateType source = .previousZero ∧ symbol = 1 := by
  have baseStep := machine.step_type step
  rw [targetType] at baseStep
  have hv : symbol.val = 0 ∨ symbol.val = 1 := by omega
  have hsym : symbol = 0 ∨ symbol = 1 := by
    rcases hv with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hsym with h0 | h1
  · subst h0
    simp [binaryZeckendorfBase] at baseStep
  · subst h1
    cases sourceType : machine.stateType source with
    | previousZero => exact ⟨rfl, rfl⟩
    | previousOne =>
        rw [sourceType] at baseStep
        simp [binaryZeckendorfBase] at baseStep

/-- A reachable previous-one state is reached on a final input `1` from a
previous-zero state. -/
theorem reachable_previousOne_has_one_predecessor
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    {target : State}
    (reachable : Reachable machine target)
    (targetType : machine.stateType target = .previousOne) :
    ∃ source : State,
      machine.stateType source = .previousZero ∧
        machine.step source (1 : Fin 2) = some target := by
  obtain ⟨word, run⟩ := reachable
  by_cases empty : word = []
  · subst word
    have targetStart : target = machine.start := by
      apply Option.some.inj
      calc
        some target = machine.run [] := run.symm
        _ = some machine.start := rfl
    subst target
    have startType : machine.stateType machine.start = .previousZero := by
      simpa [binaryZeckendorfBase] using machine.start_type
    have contradiction : False := by
      simpa [startType] using targetType
    exact contradiction.elim
  · obtain ⟨wordPrefix, symbol, decomposition⟩ :=
      word.eq_nil_or_concat.resolve_left empty
    rw [List.concat_eq_append] at decomposition
    rw [decomposition] at run
    obtain ⟨source, _, finalStep⟩ :=
      run_append_singleton_eq_some machine run
    obtain ⟨sourceType, symbolOne⟩ :=
      step_to_previousOne_has_previousZero_source
        machine finalStep targetType
    subst symbol
    exact ⟨source, sourceType, finalStep⟩

/-- Reachability supplies the one-step predecessor condition for every
previous-one state. -/
theorem allStatesReachable_implies_everyOneStateHasOnePredecessor
    {Output : Type u} {State : Type v}
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    (reachable : AllStatesReachable machine) :
    EveryOneStateHasOnePredecessor machine := by
  intro target
  obtain ⟨source, sourceType, step⟩ :=
    reachable_previousOne_has_one_predecessor
      machine (reachable target.1) target.2
  exact ⟨⟨source, sourceType⟩, step⟩

/-- Determinism makes a chosen previous-zero predecessor injective on the
previous-one fiber. Consequently, the previous-one fiber cannot be larger. -/
theorem previousOne_card_le_previousZero_card
    {Output : Type u} {State : Type v} [Fintype State]
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    (predecessor : EveryOneStateHasOnePredecessor machine) :
    Fintype.card (PreviousOneState machine) ≤
      Fintype.card (PreviousZeroState machine) := by
  classical
  choose source sourceStep using predecessor
  refine Fintype.card_le_of_injective source ?_
  intro left right sameSource
  apply Subtype.ext
  apply Option.some.inj
  calc
    some left.1 = machine.step (source left).1 (1 : Fin 2) :=
      (sourceStep left).symm
    _ = machine.step (source right).1 (1 : Fin 2) := by
      rw [sameSource]
    _ = some right.1 := sourceStep right

/-- In particular, any finite typed machine in which every state is reachable
satisfies `card(previousOne) ≤ card(previousZero)`. -/
theorem previousOne_card_le_previousZero_card_of_allStatesReachable
    {Output : Type u} {State : Type v} [Fintype State]
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    (reachable : AllStatesReachable machine) :
    Fintype.card (PreviousOneState machine) ≤
      Fintype.card (PreviousZeroState machine) :=
  previousOne_card_le_previousZero_card machine
    (allStatesReachable_implies_everyOneStateHasOnePredecessor
      machine reachable)

/-- A proposed reachable type split with more previous-one than previous-zero
states is impossible before any SAT search is run. -/
theorem not_allStatesReachable_of_previousZero_card_lt_previousOne_card
    {Output : Type u} {State : Type v} [Fintype State]
    (machine : TypedPartialDFAO binaryZeckendorfBase Output State)
    (strict :
      Fintype.card (PreviousZeroState machine) <
        Fintype.card (PreviousOneState machine)) :
    ¬AllStatesReachable machine := by
  intro reachable
  exact (Nat.not_lt_of_ge
    (previousOne_card_le_previousZero_card_of_allStatesReachable
      machine reachable)) strict

#print axioms reachable_previousOne_has_one_predecessor
#print axioms previousOne_card_le_previousZero_card_of_allStatesReachable
#print axioms not_allStatesReachable_of_previousZero_card_lt_previousOne_card

end D5.S0.Automata.TypedBinaryReachabilityCardinality
