/- GID: D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality
   generality: G
   mirror-B: D5/B/S3/Quantum/Optimization/SwapEarliestDephasingOptimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every earliest adjacent-pair swapping history minimizes accumulated dephasing. -/

import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Lattice.Fold

/-! The swapping recurrences (38) and (39) of Kamin, Shchukin, Schmidt and van Loock,
arXiv:2203.10318v1. Ready times range over all natural numbers, including the source's
positive integers. Every tie choice in the earliest-pair rule is permitted. -/

set_option autoImplicit false

namespace D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality

/-- Replace adjacent entries `i` and `i + 1` by their maximum. Only valid indices
are used by a greedy run or by the optimal-cost recurrence. -/
def merge (x : List ℕ) (i : ℕ) : List ℕ :=
  x.take i ++ max (x[i]?.getD 0) (x[i + 1]?.getD 0) :: x.drop (i + 2)

/-- The absolute difference of the two ready times, as in the source's swap cost. -/
def swapCost (x : List ℕ) (i : ℕ) : ℕ :=
  max (x[i]?.getD 0) (x[i + 1]?.getD 0) - min (x[i]?.getD 0) (x[i + 1]?.getD 0)

/-- A valid pair whose maximum ready time is minimal among all current adjacent pairs. -/
def IsGreedyStep (x : List ℕ) (i : ℕ) : Prop :=
  i + 1 < x.length ∧ ∀ j, j + 1 < x.length →
    max (x[i]?.getD 0) (x[i + 1]?.getD 0) ≤
      max (x[j]?.getD 0) (x[j + 1]?.getD 0)

/-- One Bellman step of the source's recurrence (39): the minimum over valid first
swaps of the swap cost plus the given value of the merged list, and `0` on lists
of length at most one. -/
def bellman (v : List ℕ → ℕ) (x : List ℕ) : ℕ :=
  if h : 1 < x.length then
    (Finset.range (x.length - 1)).inf'
      (Finset.nonempty_range_iff.mpr (Nat.sub_ne_zero_of_lt h))
      (fun i => swapCost x i + v (merge x i))
  else 0

/-- The source's optimal dephasing recurrence (39). Length-many Bellman steps suffice
because each valid merge decreases the length by one; lengths zero and one have cost zero. -/
def dstar (x : List ℕ) : ℕ :=
  ((bellman^[x.length]) (fun _ => 0)) x

/-- A complete history of earliest-pair merges, permitting arbitrary ties. The terminal
list has at most one entry; hence the history has exactly `x.length - 1` steps. -/
def IsGreedyRun (x : List ℕ) (hs : List ℕ) : Prop :=
  hs.foldr (fun i r y => IsGreedyStep y i ∧ r (merge y i)) (fun y => y.length ≤ 1) x

/-- Sum the absolute-difference costs along the successive merged lists. -/
def runCost (x : List ℕ) (hs : List ℕ) : ℕ :=
  hs.foldr (fun i r y => swapCost y i + r (merge y i)) (fun _ => 0) x

/-- Every complete greedy history attains the optimal dephasing, for every list length. -/
def claim : Prop :=
  ∀ (x : List ℕ) (hs : List ℕ), IsGreedyRun x hs → runCost x hs = dstar x

private def potential (x : List ℕ) : ℤ :=
  (x.foldr max 0 : ℕ) + ((x.zipWith max x.tail).sum : ℕ) - (x.sum : ℤ)

private def boundary (p : ℕ) (x : List ℕ) : ℤ :=
  ((List.zipWith max (p :: x) x).sum : ℕ) - (x.sum : ℤ)

private theorem merge_cons (a : ℕ) (x : List ℕ) (i : ℕ) :
    merge (a :: x) (i + 1) = a :: merge x i := by
  dsimp only [merge]
  simp [Nat.add_assoc]

private theorem boundary_cons (p a : ℕ) (x : List ℕ) :
    boundary p (a :: x) = (max p a : ℕ) - (a : ℤ) + boundary a x := by
  dsimp only [boundary]
  simp [Int.natCast_add]
  omega

private theorem merge_length (x : List ℕ) (i : ℕ) (h : i + 1 < x.length) :
    (merge x i).length + 1 = x.length := by
  dsimp only [merge]
  simp only [List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

private theorem maximum_merge (x : List ℕ) (i : ℕ) (h : i + 1 < x.length) :
    (merge x i).foldr max 0 = x.foldr max 0 := by
  induction i generalizing x with
  | zero =>
    cases x with
    | nil => simp at h
    | cons a x =>
      cases x with
      | nil => simp at h
      | cons b x =>
        dsimp only [merge]
        simp [max_assoc]
  | succ i ih =>
    cases x with
    | nil => simp at h
    | cons a x =>
      rw [merge_cons, List.foldr_cons, ih x (by simpa using h), List.foldr_cons]

private theorem potential_eq_boundary (x : List ℕ) :
    potential x = boundary (x.foldr max 0) x := by
  cases x with
  | nil =>
    dsimp only [potential, boundary]
    simp
  | cons a x =>
    dsimp only [potential, boundary]
    simp [Int.natCast_add]

private theorem boundary_step_le (p : ℕ) (x : List ℕ) (i : ℕ)
    (h : i + 1 < x.length) :
    boundary p x ≤ (swapCost x i : ℤ) + boundary p (merge x i) := by
  induction i generalizing p x with
  | zero =>
    cases x with
    | nil => simp at h
    | cons a x =>
      cases x with
      | nil => simp at h
      | cons b x =>
        cases x with
        | nil =>
          dsimp only [boundary, merge, swapCost]
          simp [Int.natCast_add]
          omega
        | cons c x =>
          dsimp only [boundary, merge, swapCost]
          simp [Int.natCast_add]
          omega
  | succ i ih =>
    cases x with
    | nil => simp at h
    | cons a x =>
      rw [merge_cons, boundary_cons, boundary_cons]
      have hi := ih a x (by simpa using h)
      dsimp only [swapCost] at *
      simp only [List.getElem?_cons_succ, Nat.add_assoc] at *
      omega

private theorem boundary_step_eq (p : ℕ) (x : List ℕ) (i : ℕ)
    (h : i + 1 < x.length)
    (hg : ∀ j, j + 1 < (p :: x).length →
      max (x[i]?.getD 0) (x[i + 1]?.getD 0) ≤
        max ((p :: x)[j]?.getD 0) ((p :: x)[j + 1]?.getD 0)) :
    boundary p x = (swapCost x i : ℤ) + boundary p (merge x i) := by
  induction i generalizing p x with
  | zero =>
    cases x with
    | nil => simp at h
    | cons a x =>
      cases x with
      | nil => simp at h
      | cons b x =>
        have hl := hg 0 (by simp)
        cases x with
        | nil =>
          dsimp only [boundary, merge, swapCost] at hl ⊢
          simp [Int.natCast_add] at hl ⊢
          omega
        | cons c x =>
          have hr := hg 2 (by simp)
          dsimp only [boundary, merge, swapCost] at hl hr ⊢
          simp [Int.natCast_add] at hl hr ⊢
          omega
  | succ i ih =>
    cases x with
    | nil => simp at h
    | cons a x =>
      rw [merge_cons, boundary_cons, boundary_cons]
      have hi := ih a x (by simpa using h) (fun j hj => by
        have hjg := hg (j + 1) (by simpa using Nat.succ_lt_succ hj)
        simpa [Nat.add_assoc] using hjg)
      dsimp only [swapCost] at *
      simp only [List.getElem?_cons_succ, Nat.add_assoc] at *
      omega

private theorem potential_step_le (x : List ℕ) (i : ℕ) (h : i + 1 < x.length) :
    potential x ≤ (swapCost x i : ℤ) + potential (merge x i) := by
  rw [potential_eq_boundary, potential_eq_boundary, maximum_merge x i h]
  exact boundary_step_le _ x i h

private theorem potential_step_eq (x : List ℕ) (i : ℕ) (h : IsGreedyStep x i) :
    potential x = (swapCost x i : ℤ) + potential (merge x i) := by
  rw [potential_eq_boundary, potential_eq_boundary, maximum_merge x i h.1]
  apply boundary_step_eq _ x i h.1
  intro j hj
  cases j with
  | zero =>
    have hv := h.1
    have hi : i < x.length := Nat.lt_of_succ_lt h.1
    have ha := List.le_max_of_le (List.getElem_mem hi)
      (le_rfl : x[i] ≤ x[i])
    have hb := List.le_max_of_le (List.getElem_mem h.1)
      (le_rfl : x[i + 1] ≤ x[i + 1])
    simp only [List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem h.1, Option.getD_some, List.getElem?_cons_zero,
      List.getElem?_cons_succ] at *
    exact (max_le ha hb).trans (le_max_left _ _)
  | succ j =>
    simpa [Nat.add_assoc] using h.2 j (by simpa using hj)

private theorem greedy_exists (x : List ℕ) (h : 1 < x.length) :
    ∃ i, IsGreedyStep x i := by
  have hn : (Finset.range (x.length - 1)).Nonempty :=
    Finset.nonempty_range_iff.mpr (Nat.sub_ne_zero_of_lt h)
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hn
    (fun j => max (x[j]?.getD 0) (x[j + 1]?.getD 0))
  refine ⟨i, ?_, ?_⟩
  · exact Nat.lt_sub_iff_add_lt.mp (Finset.mem_range.mp hi)
  · intro j hj
    rw [← he]
    exact Finset.inf'_le _ (Finset.mem_range.mpr (Nat.lt_sub_iff_add_lt.mpr hj))

private theorem potential_terminal (x : List ℕ) (h : x.length ≤ 1) :
    potential x = 0 := by
  cases x with
  | nil =>
    dsimp only [potential]
    simp
  | cons a x =>
    cases x with
    | nil =>
      dsimp only [potential]
      simp
    | cons b x => simp at h

private theorem bellman_potential (n : ℕ) (x : List ℕ) (h : x.length ≤ n) :
    (((bellman^[n]) (fun _ => 0)) x : ℤ) = potential x := by
  induction n generalizing x with
  | zero =>
    have hx : x = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst x
    dsimp only [potential]
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    by_cases hx : 1 < x.length
    · dsimp only [bellman]
      simp only [dite_eq_left hx]
      have hn : (Finset.range (x.length - 1)).Nonempty :=
        Finset.nonempty_range_iff.mpr (Nat.sub_ne_zero_of_lt hx)
      apply le_antisymm
      · obtain ⟨i, hi⟩ := greedy_exists x hx
        have him : i ∈ Finset.range (x.length - 1) :=
          Finset.mem_range.mpr (Nat.lt_sub_iff_add_lt.mpr hi.1)
        have hm := Finset.inf'_le
          (fun j => swapCost x j + ((bellman^[n]) (fun _ => 0)) (merge x j)) him
        have hrec := ih (merge x i) (by have := merge_length x i hi.1; omega)
        have hcast := Int.ofNat_le.mpr hm
        rw [Int.natCast_add, hrec, ← potential_step_eq x i hi] at hcast
        exact hcast
      · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hn
          (fun j => swapCost x j + ((bellman^[n]) (fun _ => 0)) (merge x j))
        have hiv : i + 1 < x.length := Nat.lt_sub_iff_add_lt.mp (Finset.mem_range.mp hi)
        rw [he, Int.natCast_add, ih (merge x i) (by have := merge_length x i hiv; omega)]
        exact potential_step_le x i hiv
    · dsimp only [bellman]
      simp only [dite_eq_right hx, Int.natCast_zero]
      exact (potential_terminal x (by omega)).symm

private theorem dstar_potential (x : List ℕ) : (dstar x : ℤ) = potential x := by
  exact bellman_potential x.length x le_rfl

private theorem greedy_cost_potential (x : List ℕ) (hs : List ℕ)
    (h : IsGreedyRun x hs) : (runCost x hs : ℤ) = potential x := by
  induction hs generalizing x with
  | nil =>
    exact (potential_terminal x h).symm
  | cons i hs ih =>
    obtain ⟨hi, ht⟩ := h
    change ((swapCost x i + runCost (merge x i) hs : ℕ) : ℤ) = _
    rw [Int.natCast_add, ih (merge x i) ht, ← potential_step_eq x i hi]

/-- The earliest-pair conjecture (41), for every number of segments and every tie choice. -/
theorem result : claim := by
  intro x hs h
  exact Int.ofNat_inj.mp ((greedy_cost_potential x hs h).trans (dstar_potential x).symm)

end D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
