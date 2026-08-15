/- GID: D5/S3/ObserverMemory/Prediction/EventualCycleAverage
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/EventualCycleAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An eventually cyclic orbit has long-run observable average equal to its cycle average. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-15):
   * Exact pinned-Mathlib hits `tendsto_mod_div_atTop_nhds_zero_nat`
     and `tendsto_natCast_div_add_atTop` control the cycle remainder and
     the finite entry prefix; both are imported and applied below.
   * `Fin.sum_univ_eq_sum_range` and `sum_range_add` are the exact finite
     reindexing results used to split complete cycles from the remainder.
   * Loogle periodicity queries found `Function.Periodic` operations but no
     discrete periodic-average limit. LeanSearch returned the convergent
     sequence Cesaro theorem, fixed-point Birkhoff averages, and shift
     differences; none proves the nonconstant periodic-orbit formula.
   * Repository and formalization-receipt searches found no equal or stronger
     eventual-cycle average declaration.
-/

open Filter Finset
open scoped BigOperators Topology

namespace D5.S3.ObserverMemory.Prediction.EventualCycleAverage

private theorem sum_cycle_blocks
    {period : Nat} (hperiod : 0 < period)
    (value : Fin period -> Real) (q : Nat) :
    (∑ i ∈ range (q * period),
      value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) =
      (q : Real) * ∑ i ∈ range period,
        value (Fin.mk (i % period) (Nat.mod_lt i hperiod)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.succ_mul, sum_range_add, ih]
      have hblock :
          (∑ x ∈ range period,
            value (Fin.mk ((q * period + x) % period)
              (Nat.mod_lt (q * period + x) hperiod))) =
            ∑ x ∈ range period,
              value (Fin.mk (x % period) (Nat.mod_lt x hperiod)) := by
        apply sum_congr rfl
        intro x hx
        congr 1
        simp [Nat.add_mod]
      rw [hblock]
      push_cast
      ring

private theorem sum_cycle_mod_eq_blocks_remainder
    {period : Nat} (hperiod : 0 < period)
    (value : Fin period -> Real) (n : Nat) :
    (∑ i ∈ range n,
      value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) =
      ((n / period : Nat) : Real) *
          (∑ i ∈ range period,
            value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) +
        ∑ i ∈ range (n % period),
          value (Fin.mk (i % period) (Nat.mod_lt i hperiod)) := by
  nth_rw 1 [<- Nat.div_add_mod n period]
  rw [Nat.mul_comm period (n / period)]
  rw [sum_range_add, sum_cycle_blocks hperiod value]
  congr 1
  apply sum_congr rfl
  intro i hi
  congr 1
  simp [Nat.add_mod]

private theorem cycle_average
    {period : Nat} (hperiod : 0 < period)
    (value : Fin period -> Real) :
    Tendsto
      (fun n : Nat =>
        (∑ i ∈ range n,
          value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) / (n : Real))
      atTop
      (nhds ((∑ j : Fin period, value j) / (period : Real))) := by
  let total : Real := ∑ i ∈ range period,
    value (Fin.mk (i % period) (Nat.mod_lt i hperiod))
  let remainder : Nat -> Real := fun n =>
    ∑ i ∈ range (n % period),
      value (Fin.mk (i % period) (Nat.mod_lt i hperiod))
  have hsum (n : Nat) :
      (∑ i ∈ range n,
        value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) =
        ((n / period : Nat) : Real) * total + remainder n := by
    simpa [total, remainder] using
      sum_cycle_mod_eq_blocks_remainder hperiod value n
  have hmod :
      Tendsto (fun n : Nat => ((n % period : Nat) : Real) / (n : Real))
        atTop (nhds 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hperiod
  have hmain :
      Tendsto
        (fun n : Nat =>
          (total / (period : Real)) *
            (1 - ((n % period : Nat) : Real) / (n : Real)))
        atTop (nhds (total / (period : Real))) := by
    simpa using (tendsto_const_nhds (x := (1 : Real))).sub hmod |>.const_mul
      (total / (period : Real))
  let bound : Real := ∑ i ∈ range period,
    norm (value (Fin.mk (i % period) (Nat.mod_lt i hperiod)))
  have hbound (n : Nat) : norm (remainder n) <= bound := by
    calc
      norm (remainder n) <=
          ∑ i ∈ range (n % period),
            norm (value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) := by
        simp only [remainder]
        exact norm_sum_le _ _
      _ <= ∑ i ∈ range period,
          norm (value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) := by
        exact sum_le_sum_of_subset_of_nonneg
          (range_mono (Nat.le_of_lt (Nat.mod_lt n hperiod)))
          (fun _ _ _ => norm_nonneg _)
      _ = bound := by rfl
  have hrem : Tendsto (fun n : Nat => remainder n / (n : Real)) atTop (nhds 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
    · filter_upwards with n
      exact neg_le_of_abs_le (hbound n)
    · filter_upwards with n
      exact (le_abs_self _).trans (hbound n)
    · exact tendsto_natCast_atTop_atTop
  have havg : Tendsto
      (fun n : Nat =>
        (∑ i ∈ range n,
          value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) / (n : Real))
      atTop (nhds (total / (period : Real))) := by
    have heq :
        (fun n : Nat =>
          (total / (period : Real)) *
              (1 - ((n % period : Nat) : Real) / (n : Real)) +
            remainder n / (n : Real)) =ᶠ[atTop]
          (fun n : Nat =>
            (∑ i ∈ range n,
              value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) / (n : Real)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hsum]
      have hn0 : (n : Real) ≠ 0 := by positivity
      have hp0 : (period : Real) ≠ 0 := by positivity
      have hdecomp : (n : Real) =
          ((n / period : Nat) : Real) * (period : Real) +
            ((n % period : Nat) : Real) := by
        have hnat : n = n / period * period + n % period := by
          simpa [Nat.mul_comm] using (Nat.div_add_mod n period).symm
        exact_mod_cast hnat
      field_simp
      rw [hdecomp]
      ring
    simpa only [add_zero] using (hmain.add hrem).congr' heq
  have hfin : total = ∑ j : Fin period, value j := by
    have h := Fin.sum_univ_eq_sum_range
      (fun i : Nat => value (Fin.mk (i % period) (Nat.mod_lt i hperiod))) period
    simpa [total, Nat.mod_eq_of_lt] using h.symm
  simpa [hfin] using havg

/-- Once an orbit enters a finite cycle, the long-run average of every
real-valued observable is the uniform average of its values on that cycle. -/
theorem eventual_cycle_average
    {Y : Type*} (update : Y -> Y) (value : Y -> Real) (initial : Y)
    {period : Nat} (hperiod : 0 < period)
    (cycle : Fin period -> Y) (entry : Nat)
    (hcycle : forall n : Nat,
      (update^[entry + n]) initial =
        cycle (Fin.mk (n % period) (Nat.mod_lt n hperiod))) :
    Tendsto
      (fun horizon : Nat =>
        (∑ time ∈ range horizon, value ((update^[time]) initial)) /
          (horizon : Real))
      atTop
      (nhds ((∑ j : Fin period, value (cycle j)) / (period : Real))) := by
  let orbitValue : Nat -> Real := fun time => value ((update^[time]) initial)
  let cycleValue : Fin period -> Real := fun j => value (cycle j)
  have hperiodic := cycle_average hperiod cycleValue
  apply (tendsto_add_atTop_iff_nat entry).mp
  have hratio :
      Tendsto (fun n : Nat => (n : Real) / (n + entry : Nat)) atTop (nhds 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_natCast_div_add_atTop (entry : Real))
  have hscaled := hperiodic.mul hratio
  have hprefix :
      Tendsto
        (fun n : Nat =>
          (∑ time ∈ range entry, orbitValue time) / (n + entry : Nat))
        atTop (nhds 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
    · exact Eventually.of_forall (fun _ => le_rfl)
    · exact Eventually.of_forall (fun _ => le_rfl)
    · exact (tendsto_natCast_atTop_atTop (R := Real)).comp
        ((tendsto_add_atTop_iff_nat entry).2 tendsto_id)
  have hcombined := hprefix.add hscaled
  have heq :
      (fun n : Nat =>
        (∑ time ∈ range entry, orbitValue time) / (n + entry : Nat) +
          (∑ i ∈ range n,
            cycleValue (Fin.mk (i % period) (Nat.mod_lt i hperiod))) / (n : Real) *
              ((n : Real) / (n + entry : Nat))) =ᶠ[atTop]
        (fun n : Nat =>
          (∑ time ∈ range (n + entry), orbitValue time) / (n + entry : Nat)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [show n + entry = entry + n by omega, sum_range_add]
    have htail :
        (∑ time ∈ range n, orbitValue (entry + time)) =
          ∑ time ∈ range n,
            cycleValue (Fin.mk (time % period) (Nat.mod_lt time hperiod)) := by
      apply sum_congr rfl
      intro time _
      simp only [orbitValue, cycleValue]
      rw [hcycle time]
    rw [htail]
    have hn0 : (n : Real) ≠ 0 := by positivity
    have hne0 : ((n + entry : Nat) : Real) ≠ 0 := by positivity
    field_simp
  simpa only [cycleValue, orbitValue, one_mul, mul_one, zero_add] using
    hcombined.congr' heq

/-- A fixed Boolean state and a one-point cycle witness satisfiable hypotheses. -/
example :
    Tendsto
      (fun horizon : Nat =>
        (∑ time ∈ range horizon,
          if (((id : Bool -> Bool)^[time]) false) then (1 : Real) else 0) /
          (horizon : Real))
      atTop (nhds 0) := by
  convert eventual_cycle_average
    (update := id) (value := fun state : Bool => if state then 1 else 0)
    (initial := false) (period := 1) (Nat.zero_lt_succ 0)
    (fun _ => false) 0 (fun n => by simp) using 1
  all_goals simp

end D5.S3.ObserverMemory.Prediction.EventualCycleAverage
