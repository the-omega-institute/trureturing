/- GID: D5/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiniteInputGeneratorPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite deterministic input generator makes every extended orbit eventually periodic. -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib hit: `Finite.exists_ne_map_eq_of_infinite` gives a
     collision in the orbit map from the naturals to the finite product state;
     it is imported from `Mathlib.Data.Fintype.Pigeonhole` and applied below.
   * Loogle also found `EquivFin.not_injective_infinite_finite`; LeanSearch found
     the nearby `Function.Injective.mem_periodicPts`, which is inapplicable to
     arbitrary noninjective updates, but no exact eventual-periodicity theorem.
   * Repository and formalization searches found no declaration with the full
     finite-generator product update and eventual-periodicity conclusion. -/

namespace D5.S3.ObserverMemory.Prediction.FiniteInputGeneratorPeriodicity

/-- Coupling a finite state with a finite deterministic input generator yields
an autonomous product update whose orbit from every initial state is eventually
periodic. -/
theorem finite_input_generator_eventually_periodic
    {Y C U : Type*} [Finite Y] [Finite C]
    (F : U -> Y -> Y) (J : C -> C) (g : C -> U)
    (initial : Y × C) :
    ∃ mu period : Nat, 0 < period ∧
      ∀ t : Nat,
        ((fun state : Y × C =>
          (F (g state.2) state.1, J state.2))^[mu + t + period]) initial =
        ((fun state : Y × C =>
          (F (g state.2) state.1, J state.2))^[mu + t]) initial := by
  let step : Y × C -> Y × C := fun state =>
    (F (g state.2) state.1, J state.2)
  obtain ⟨i, j, hij, horbit⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n : Nat => (step^[n]) initial)
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · refine ⟨i, j - i, by omega, ?_⟩
    intro t
    change (step^[i + t + (j - i)]) initial = (step^[i + t]) initial
    calc
      (step^[i + t + (j - i)]) initial =
          (step^[t]) ((step^[j]) initial) := by
            rw [show i + t + (j - i) = t + j by omega,
              Function.iterate_add_apply]
      _ = (step^[t]) ((step^[i]) initial) := congrArg (step^[t]) horbit.symm
      _ = (step^[i + t]) initial := by
        rw [show i + t = t + i by omega, Function.iterate_add_apply]
  · refine ⟨j, i - j, by omega, ?_⟩
    intro t
    change (step^[j + t + (i - j)]) initial = (step^[j + t]) initial
    calc
      (step^[j + t + (i - j)]) initial =
          (step^[t]) ((step^[i]) initial) := by
            rw [show j + t + (i - j) = t + i by omega,
              Function.iterate_add_apply]
      _ = (step^[t]) ((step^[j]) initial) := congrArg (step^[t]) horbit
      _ = (step^[j + t]) initial := by
        rw [show j + t = t + j by omega, Function.iterate_add_apply]

/-- A Boolean input generator supplies checked finite carriers, maps, and an
inhabited product-state domain for the theorem. -/
example :
    ∃ mu period : Nat, 0 < period ∧
      ∀ t : Nat,
        ((fun state : Bool × Bool =>
          (state.2, !state.2))^[mu + t + period]) (false, false) =
        ((fun state : Bool × Bool =>
          (state.2, !state.2))^[mu + t]) (false, false) := by
  exact finite_input_generator_eventually_periodic
    (F := fun input (_ : Bool) => input)
    (J := fun control : Bool => !control)
    (g := id)
    (false, false)

end D5.S3.ObserverMemory.Prediction.FiniteInputGeneratorPeriodicity
