/- GID: D5/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/RankCuts/RankedIntervalParity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bound changes of strict crossing parity by twice the number of rank intervals. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

open Finset

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity

variable {ι : Type*} [Fintype ι] {n : ℕ}

private def beforeWeight (start stop : ι → Fin (n + 1)) (b : Fin (n + 1)) (i : ι) : ℕ :=
  if (start i).val < b.val ∧ b.val ≤ (stop i).val then 1 else 0

private def afterWeight (start stop : ι → Fin (n + 1)) (b : Fin (n + 1)) (i : ι) : ℕ :=
  if (start i).val ≤ b.val ∧ b.val < (stop i).val then 1 else 0

private def endpointWeight (start stop : ι → Fin (n + 1)) (b : Fin (n + 1)) (i : ι) : ℕ :=
  (if start i = b then 1 else 0) + (if stop i = b then 1 else 0)

/-- Count changes in coverage parity across the boundaries of the observation list. -/
private def parityChanges (start stop : ι → Fin (n + 1)) : ℕ :=
  ∑ b : Fin (n + 1), if (∑ i, beforeWeight start stop b i) % 2 =
    (∑ i, afterWeight start stop b i) % 2 then 0 else 1

omit [Fintype ι] in
private theorem same_without_endpoint (start stop : ι → Fin (n + 1)) (b : Fin (n + 1))
    (i : ι) (hs : start i ≠ b) (ht : stop i ≠ b) :
    beforeWeight start stop b i = afterWeight start stop b i := by
  have hs' : (start i).val ≠ b.val := fun h => hs (Fin.ext h)
  have ht' : (stop i).val ≠ b.val := fun h => ht (Fin.ext h)
  have equivalent : ((start i).val < b.val ∧ b.val ≤ (stop i).val) ↔
      (start i).val ≤ b.val ∧ b.val < (stop i).val := by omega
  simp only [beforeWeight, afterWeight, equivalent]

/-- A change in the parity of coverage needs an endpoint at that boundary. -/
private theorem parity_changes_le_twice_intervals (start stop : ι → Fin (n + 1)) :
    parityChanges start stop ≤ 2 * Fintype.card ι := by
  unfold parityChanges
  calc
    _ ≤ ∑ b : Fin (n + 1), ∑ i, endpointWeight start stop b i := by
      apply sum_le_sum
      intro b _
      split
      · omega
      next different =>
        by_contra! h
        have zero : (∑ i, endpointWeight start stop b i) = 0 := by omega
        have equal : (∑ i, beforeWeight start stop b i) = ∑ i, afterWeight start stop b i := by
          apply sum_congr rfl
          intro i _
          have hle := single_le_sum (f := endpointWeight start stop b)
            (fun _ _ => Nat.zero_le _) (mem_univ i)
          have noEndpoint : endpointWeight start stop b i = 0 := by omega
          have hs : start i ≠ b := by
            intro he
            simp [endpointWeight, he] at noEndpoint
          have ht : stop i ≠ b := by
            intro he
            simp [endpointWeight, he] at noEndpoint
          exact same_without_endpoint start stop b i hs ht
        exact different (congrArg (fun k => k % 2) equal)
    _ = 2 * Fintype.card ι := by
      rw [sum_comm]
      simp only [endpointWeight, sum_add_distrib]
      have each (t : Fin (n + 1)) : (∑ b : Fin (n + 1), if t = b then 1 else 0) = 1 := by
        simp
      simp [each, two_mul]

private theorem threshold_count_le (P : Fin n → Prop) [DecidablePred P]
    (lower : ∀ i j : Fin n, i ≤ j → P j → P i) (j : Fin n) :
    (univ.filter P).card ≤ j.val ↔ ¬ P j := by
  constructor
  · intro small hj
    have sub : Iic j ⊆ univ.filter P := by
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _, lower i j (mem_Iic.mp hi) hj⟩
    have big := card_le_card sub
    rw [Fin.card_Iic] at big
    omega
  · intro hj
    have sub : univ.filter P ⊆ Iio j := by
      intro i hi
      apply mem_Iio.mpr
      by_contra! ge
      exact hj (lower j i ge (mem_filter.mp hi).2)
    simpa [Fin.card_Iio] using card_le_card sub

private def threshold (P : Fin n → Prop) [DecidablePred P] : Fin (n + 1) :=
  ⟨(univ.filter P).card, Nat.lt_succ_of_le (by
    simpa using (card_filter_le (s := (univ : Finset (Fin n))) (p := P)))⟩

private def realCount (cuts : Fin n → ℕ) (lo hi : ι → ℕ) (j : Fin n) : ℕ :=
  ∑ i, if lo i < cuts j ∧ cuts j < hi i then 1 else 0

/-- Strict crossing parity on the ordered cuts at slots one through `n`,
with zero at the end slots and outside the observation list. -/
def paddedParity (cuts : Fin n → ℕ) (lo hi : ι → ℕ) (slot : ℕ) : ℕ :=
  if h : 0 < slot ∧ slot ≤ n then
    realCount cuts lo hi ⟨slot - 1, by omega⟩ % 2
  else 0

/-- Each rank interval contributes at most two endpoints to the padded sequence of cut parities. -/
theorem changes_le_twice_jumps (cuts : Fin n → ℕ) (monotone : Monotone cuts)
    (lo hi : ι → ℕ) :
    (∑ b : Fin (n + 1), if paddedParity cuts lo hi b.val =
      paddedParity cuts lo hi (b.val + 1) then 0 else 1) ≤ 2 * Fintype.card ι := by
  let start (i : ι) := threshold (fun j => cuts j ≤ lo i)
  let stop (i : ι) := threshold (fun j => cuts j < hi i)
  have hstart (i : ι) (j : Fin n) : (start i).val ≤ j.val ↔ lo i < cuts j := by
    exact (threshold_count_le _ (fun a b h hab => (monotone h).trans hab) j).trans not_le
  have hstop (i : ι) (j : Fin n) : j.val < (stop i).val ↔ cuts j < hi i := by
    have e := threshold_count_le (fun a => cuts a < hi i)
      (fun a b h hab => lt_of_le_of_lt (monotone h) hab) j
    change (stop i).val ≤ j.val ↔ ¬ cuts j < hi i at e
    exact not_le.symm.trans ((not_congr e).trans not_not)
  have after (b : Fin (n + 1)) : (∑ i, afterWeight start stop b i) % 2 =
      paddedParity cuts lo hi (b.val + 1) := by
    by_cases hb : b.val < n
    · have good : 0 < b.val + 1 ∧ b.val + 1 ≤ n := by omega
      rw [paddedParity, dite_eq_left good]
      congr 1
      unfold realCount
      apply sum_congr rfl
      intro i _
      let j : Fin n := ⟨b.val, hb⟩
      change (if (start i).val ≤ j.val ∧ j.val < (stop i).val then 1 else 0) =
        (if lo i < cuts j ∧ cuts j < hi i then 1 else 0)
      simp only [hstart, hstop]
    · have bad : ¬ (0 < b.val + 1 ∧ b.val + 1 ≤ n) := by omega
      rw [paddedParity, dite_eq_right bad]
      have empty (i : ι) : afterWeight start stop b i = 0 := by
        have cap := (stop i).isLt
        unfold afterWeight
        rw [ite_eq_right (by omega)]
      simp [empty]
  have before (b : Fin (n + 1)) : (∑ i, beforeWeight start stop b i) % 2 =
      paddedParity cuts lo hi b.val := by
    by_cases hb : 0 < b.val
    · have good : 0 < b.val ∧ b.val ≤ n := ⟨hb, Nat.le_of_lt_succ b.isLt⟩
      rw [paddedParity, dite_eq_left good]
      congr 1
      unfold realCount
      apply sum_congr rfl
      intro i _
      let j : Fin n := ⟨b.val - 1, by omega⟩
      have pred : j.val + 1 = b.val := by
        change b.val - 1 + 1 = b.val
        omega
      have left : (start i).val < b.val ↔ (start i).val ≤ j.val := by omega
      have right : b.val ≤ (stop i).val ↔ j.val < (stop i).val := by omega
      unfold beforeWeight
      change (if (start i).val < b.val ∧ b.val ≤ (stop i).val then 1 else 0) =
        (if lo i < cuts j ∧ cuts j < hi i then 1 else 0)
      simp only [left, right, hstart, hstop]
    · have bad : ¬ (0 < b.val ∧ b.val ≤ n) := fun h => hb h.1
      rw [paddedParity, dite_eq_right bad]
      have empty (i : ι) : beforeWeight start stop b i = 0 := by
        unfold beforeWeight
        rw [ite_eq_right (by omega)]
      simp [empty]
  have bound := parity_changes_le_twice_intervals start stop
  unfold parityChanges at bound
  simpa only [before, after] using bound

end D5.S3.Combinatorics.Graph.RankCuts.RankedIntervalParity
