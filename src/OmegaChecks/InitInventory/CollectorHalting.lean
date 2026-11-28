module

public import Mathlib.Computability.Halting
public import OmegaChecks.InitInventory.Collector
public import OmegaChecks.InitInventory.StringSearchLoops
import all Init.Data.Slice.Operations
import all Init.Data.Iterators.ToIterator

/-! Computability boundary for the official iterator interface, in pinned Mathlib. -/

public section

namespace OmegaChecks.InitBoundaries.Collector
open Nat.Partrec (Code)
open Std Std.Iterators

private theorem boundedSignal_iff_halts (c : Code) (input : Nat) :
    (∃ fuel, (Code.evaln fuel c input).isSome = true) ↔ (c.eval input).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨fuel, hit⟩
    obtain ⟨value, h⟩ := Option.isSome_iff_exists.mp hit
    exact ⟨value, Code.evaln_complete.mpr ⟨fuel, h⟩⟩
  · rintro ⟨value, h⟩
    obtain ⟨fuel, hit⟩ := Code.evaln_complete.mp h
    exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨value, hit⟩⟩

/-- The raw finiteness bit required by the pinned `Take.Rel.eq_1` is noncomputable
on bounded simulations, even with natural-number states, unit outputs and no skips. -/
theorem not_computable_take_finiteness_bit
    (classify : ∀ [Iterator Nat Id Unit] [Productive Nat Id], Decidable (Finite Nat Id))
    (input : Nat) : ¬ Computable (fun c : Code =>
      takeSearchBit (@classify) (fun fuel => (Code.evaln fuel c input).isSome)) := by
  intro computes
  apply ComputablePred.halting_problem input
  apply ComputablePred.of_eq (p := fun c : Code =>
    takeSearchBit (@classify) (fun fuel => (Code.evaln fuel c input).isSome) = true)
  · exact ⟨inferInstance, by simpa using computes⟩
  · intro c
    exact (takeSearchBit_iff (@classify) _).trans (boundedSignal_iff_halts c input)

/-- On the bounded-evaluation streams of partial recursive codes, any total collector
agreeing with the pinned finite collector yields a Boolean test outside the computable
functions. The input of each simulated code may be fixed in advance. -/
theorem not_computable_collector_halting_test
    (collect : type_of% (@Std.Iter.toList.{0}))
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      collect it = it.toList) (input : Nat) :
    ¬ Computable (fun c : Code =>
      let signal := fun fuel => (Code.evaln fuel c input).isSome
      @decide (∃ fuel, signal fuel = true)
        (limitedOmniscienceFromCollector @collect correct signal)) := by
  intro computable
  apply ComputablePred.halting_problem input
  apply ComputablePred.of_eq _ (fun c => boundedSignal_iff_halts c input)
  exact ⟨fun c => limitedOmniscienceFromCollector @collect correct
    (fun fuel => (Code.evaln fuel c input).isSome), computable⟩

/-- A total observation locating a hit of every monotone Boolean signal bounds a halting computation. -/
private theorem not_computable_signal_bound (observe : (Nat → Bool) → Nat)
    (detects : ∀ (g : Nat → Bool), (∀ i, g i = true → g (i+1) = true) →
      ∀ {n}, g n = true → g (observe g) = true) (input : Nat) :
    ¬ Computable (fun c : Code => observe (fun fuel => (Code.evaln fuel c input).isSome)) := by
  intro computable
  let bound := fun c : Code =>
    observe (fun fuel => (Code.evaln fuel c input).isSome)
  have test : Computable (fun c : Code => (Code.evaln (bound c) c input).isSome) :=
    Primrec.option_isSome.to_comp.comp
      (Code.primrec_evaln.to_comp.comp
        ((computable.pair Computable.id).pair (Computable.const input)))
  apply ComputablePred.halting_problem input
  apply ComputablePred.of_eq (p := fun c : Code => (Code.evaln (bound c) c input).isSome = true)
  · exact ⟨inferInstance, by simpa using test⟩
  · intro c
    constructor
    · exact fun hit => (boundedSignal_iff_halts c input).mp ⟨_, hit⟩
    · intro halts
      obtain ⟨k, hit⟩ := (boundedSignal_iff_halts c input).mpr halts
      refine detects
        (fun fuel => (Code.evaln fuel c input).isSome) (fun i before => ?_) (n := k) hit
      obtain ⟨value, h⟩ := Option.isSome_iff_exists.mp before
      exact Option.isSome_iff_exists.mpr ⟨value, Code.evaln_mono (Nat.le_succ i) h⟩

/-- Even the length of the output on a single family of bounded-evaluation iterators
is not a computable function of the partial recursive program. -/
theorem not_computable_search_output_length
    (measure : ∀ {α β : Type} [Iterator α Id β], Iter (α := α) β → Nat)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      measure it = it.toList.length) (input : Nat) :
    ¬ Computable (fun c : Code =>
      searchOutputLength (@measure) (fun fuel => (Code.evaln fuel c input).isSome)) :=
  not_computable_signal_bound _ (signalAtSearchOutputLength (@measure) correct) input

/-- Use the iterator itself as the representation of a slice, with its original step function. -/
def iteratorSliceLength
    (measure : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β], Slice γ → Nat)
    {α β : Type} [Iterator α Id β] (it : Iter (α := α) β) : Nat :=
  letI := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
  measure (Slice.mk it)

/-- A total slice observation that gives the pinned list length on all finite slices
has a noncomputable output length on the bounded simulations of partial recursive codes. -/
theorem not_computable_slice_output_length
    (measure : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β], Slice γ → Nat)
    (correct : ∀ {γ α β : Type} [ToIterator (Slice γ) Id α β] [Iterator α Id β] [Finite α Id]
      (s : Slice γ), measure s = s.toList.length) (input : Nat) :
    ¬ Computable (fun c : Code =>
      searchOutputLength (@iteratorSliceLength @measure) (fun fuel => (Code.evaln fuel c input).isSome)) := by
  apply not_computable_search_output_length
  intro α β iter fin it
  let _ := ToIterator.of (γ := Slice (Iter (α := α) β)) α (fun s => s.internalRepresentation)
  exact correct (Slice.mk it)

open String.Slice.Pattern

/-- The raw accumulator from a zero-width forward search on a single byte can bound
a halting computation for every program, even at a fixed input. -/
theorem not_computable_forward_stop_index
    (run : type_of% @ToForwardSearcher.DefaultForwardSearcher.instIteratorLoopIdSearchStep)
    (correct : ∀ {ρ : Type} (pat : ρ) {s : String.Slice} [inst : ForwardPattern pat],
      letI := @run ρ pat s inst
      LawfulIteratorLoop (ToForwardSearcher.DefaultForwardSearcher pat s) Id Id) (input : Nat) :
    ¬ Computable (fun c : Code => forwardStopIndex @run (fun fuel => (Code.evaln fuel c input).isSome)) :=
  not_computable_signal_bound _ (fun _ => hitAtForwardStopIndex @run correct) input

/-- The raw accumulator from a zero-width backward search on a single byte can bound
a halting computation for every program, even at a fixed input. -/
theorem not_computable_backward_stop_index
    (run : type_of% @ToBackwardSearcher.DefaultBackwardSearcher.instIteratorLoopIdSearchStep)
    (correct : ∀ {ρ : Type} (pat : ρ) {s : String.Slice} [inst : BackwardPattern pat],
      letI := @run ρ pat s inst
      LawfulIteratorLoop (ToBackwardSearcher.DefaultBackwardSearcher pat s) Id Id) (input : Nat) :
    ¬ Computable (fun c : Code => backwardStopIndex @run (fun fuel => (Code.evaln fuel c input).isSome)) :=
  not_computable_signal_bound _ (fun _ => hitAtBackwardStopIndex @run correct) input

end OmegaChecks.InitBoundaries.Collector
