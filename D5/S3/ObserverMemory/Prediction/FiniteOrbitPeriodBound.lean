/- GID: D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite orbits and readouts are eventually periodic within the state bound. -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/- Library-search audit trail (2026-08-16):
   * Exact pinned-Mathlib hit: `Fintype.exists_ne_map_eq_of_card_lt` finds a
     collision among the first `Fintype.card Y + 1` orbit points; it is
     imported from `Mathlib.Data.Fintype.Pigeonhole` and applied below.
   * `Function.iterate_add_apply` is the exact iterate-composition result used
     to propagate that collision through the entire tail.
   * Loogle confirmed the pigeonhole declaration by exact name. Searches of
     pinned Mathlib found periodic-point results but no theorem with the full
     arbitrary-map eventual-periodicity conclusion and cardinality bound.
   * LeanSearch's `/api/search` endpoint returned HTTP 404, so it supplied no
     search conclusion. Repository and receipt searches found no equal or
     stronger existing D5 declaration for the quantitative bound. -/

namespace D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound

/-- Every orbit of a self-map on a finite type enters a positive-length cycle
within at most the cardinality of the state space. Every deterministic readout
inherits the same eventual period. -/
theorem finite_orbit_and_readout_eventually_periodic
    {Y O : Type*} [Fintype Y] (F : Y -> Y) (q : Y -> O) (initial : Y) :
    exists mu period : Nat,
      0 < period /\
        mu + period <= Fintype.card Y /\
          forall t : Nat, mu <= t ->
            (F^[t + period]) initial = (F^[t]) initial /\
              q ((F^[t + period]) initial) = q ((F^[t]) initial) := by
  classical
  obtain ⟨i, j, hij, horbit⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card Y + 1) => (F^[n.val]) initial)
      (by simp)
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · refine ⟨i.val, j.val - i.val, by omega, by omega, ?_⟩
    intro t hit
    have hstate :
        (F^[t + (j.val - i.val)]) initial = (F^[t]) initial := by
      calc
        (F^[t + (j.val - i.val)]) initial =
            (F^[t - i.val]) ((F^[j.val]) initial) := by
          rw [show t + (j.val - i.val) = (t - i.val) + j.val by omega,
            Function.iterate_add_apply]
        _ = (F^[t - i.val]) ((F^[i.val]) initial) :=
          congrArg (F^[t - i.val]) horbit.symm
        _ = (F^[t]) initial := by
          rw [<- Function.iterate_add_apply, Nat.sub_add_cancel hit]
    exact ⟨hstate, congrArg q hstate⟩
  · refine ⟨j.val, i.val - j.val, by omega, by omega, ?_⟩
    intro t hjt
    have hstate :
        (F^[t + (i.val - j.val)]) initial = (F^[t]) initial := by
      calc
        (F^[t + (i.val - j.val)]) initial =
            (F^[t - j.val]) ((F^[i.val]) initial) := by
          rw [show t + (i.val - j.val) = (t - j.val) + i.val by omega,
            Function.iterate_add_apply]
        _ = (F^[t - j.val]) ((F^[j.val]) initial) :=
          congrArg (F^[t - j.val]) horbit
        _ = (F^[t]) initial := by
          rw [<- Function.iterate_add_apply, Nat.sub_add_cancel hjt]
    exact ⟨hstate, congrArg q hstate⟩

end D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
