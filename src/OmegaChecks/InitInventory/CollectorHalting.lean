module

public import Mathlib.Computability.Halting
public import OmegaChecks.InitInventory.Collector

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

end OmegaChecks.InitBoundaries.Collector
