/- GID: D5/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/StableImagePeriodicCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite self-map images decrease and stabilize exactly at the periodic core. -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Tactic

/- Library-search audit trail (2026-08-16):
   * Pinned Mathlib supplies `Function.periodicPts_subset_range`,
     `Function.IsPeriodicPt.iterate`, `Function.IsPeriodicPt.apply_iterate`, and
     `Fintype.exists_ne_map_eq_of_card_lt`; all are applied below.
   * Pinned-Mathlib text search and two local `smart_search.sh` queries found no declaration
     identifying the stable iterate range of a finite self-map with its periodic points.
   * Loogle returned zero matches for two type-pattern searches. GitHub Lean code search returned
     only the same Mathlib periodic-point building blocks and mirrors. LeanSearch's `/api/search`
     endpoint returned HTTP 404, so it supplied no search conclusion. Repository and receipt
     searches found no equal or stronger D5 declaration for stable iterate ranges. -/

namespace D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore

private theorem iterate_range_antitone
    {Y : Type*} (F : Y -> Y) {m n : Nat} (hmn : m <= n) :
    Set.range (F^[n]) ⊆ Set.range (F^[m]) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(F^[n - m]) x, ?_⟩
  rw [<- Function.iterate_add_apply, show m + (n - m) = n by omega]

/-- For a self-map of a finite carrier, the cardinalities of the iterated images decrease.
After at most the number of states, the image is exactly the set of periodic points. -/
theorem iterate_range_card_antitone_and_stable
    {Y : Type*} [Fintype Y] (F : Y -> Y) :
    Antitone (fun t : Nat => (Set.range (F^[t])).ncard) /\
      forall t : Nat, Fintype.card Y <= t ->
        Set.range (F^[t]) = Function.periodicPts F := by
  classical
  constructor
  · intro m n hmn
    exact Set.ncard_le_ncard (iterate_range_antitone F hmn)
  · intro t ht
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := iterate_range_antitone F ht hy
      obtain ⟨i, j, hij, horbit⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt
          (fun k : Fin (Fintype.card Y + 1) => (F^[k.val]) x)
          (by simp)
      rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
      · have hi_card : i.val <= Fintype.card Y := by omega
        have hperiod :
            Function.IsPeriodicPt F (j.val - i.val) ((F^[i.val]) x) := by
          change (F^[j.val - i.val]) ((F^[i.val]) x) = (F^[i.val]) x
          calc
            (F^[j.val - i.val]) ((F^[i.val]) x) = (F^[j.val]) x := by
              rw [<- Function.iterate_add_apply, Nat.sub_add_cancel hij_lt.le]
            _ = (F^[i.val]) x := horbit.symm
        have hperiod_at_card := hperiod.apply_iterate (Fintype.card Y - i.val)
        rw [<- Function.iterate_add_apply, Nat.sub_add_cancel hi_card] at hperiod_at_card
        exact Function.mk_mem_periodicPts (by omega) hperiod_at_card
      · have hj_card : j.val <= Fintype.card Y := by omega
        have hperiod :
            Function.IsPeriodicPt F (i.val - j.val) ((F^[j.val]) x) := by
          change (F^[i.val - j.val]) ((F^[j.val]) x) = (F^[j.val]) x
          calc
            (F^[i.val - j.val]) ((F^[j.val]) x) = (F^[i.val]) x := by
              rw [<- Function.iterate_add_apply, Nat.sub_add_cancel hji_lt.le]
            _ = (F^[j.val]) x := horbit
        have hperiod_at_card := hperiod.apply_iterate (Fintype.card Y - j.val)
        rw [<- Function.iterate_add_apply, Nat.sub_add_cancel hj_card] at hperiod_at_card
        exact Function.mk_mem_periodicPts (by omega) hperiod_at_card
    · intro y hy
      rcases hy with ⟨period, hperiod_pos, hperiod⟩
      apply Function.periodicPts_subset_range
      exact Function.mk_mem_periodicPts hperiod_pos (hperiod.iterate t)

#print axioms iterate_range_card_antitone_and_stable

end D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore
