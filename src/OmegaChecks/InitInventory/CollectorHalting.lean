module

public import Mathlib.Computability.Halting
public import OmegaChecks.InitInventory.Collector
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

/-- Even the length of the output on a single family of bounded-evaluation iterators
is not a computable function of the partial recursive program. -/
theorem not_computable_search_output_length
    (measure : ∀ {α β : Type} [Iterator α Id β], Iter (α := α) β → Nat)
    (correct : ∀ {α β : Type} [Iterator α Id β] [Finite α Id] (it : Iter (α := α) β),
      measure it = it.toList.length) (input : Nat) :
    ¬ Computable (fun c : Code =>
      searchOutputLength (@measure) (fun fuel => (Code.evaln fuel c input).isSome)) := by
  intro computable
  let bound := fun c : Code =>
    searchOutputLength (@measure) (fun fuel => (Code.evaln fuel c input).isSome)
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
      refine signalAtSearchOutputLength (@measure) correct
        (fun fuel => (Code.evaln fuel c input).isSome) (fun i before => ?_) (n := k) hit
      obtain ⟨value, h⟩ := Option.isSome_iff_exists.mp before
      exact Option.isSome_iff_exists.mpr ⟨value, Code.evaln_mono (Nat.le_succ i) h⟩

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

end OmegaChecks.InitBoundaries.Collector
