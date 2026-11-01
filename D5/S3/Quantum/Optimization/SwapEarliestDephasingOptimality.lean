/- GID: D5/S3/Quantum/Optimization/SwapEarliestDephasingOptimality
   generality: G
   mirror-B: D5/B/S3/Quantum/Optimization/SwapEarliestDephasingOptimality
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every earliest adjacent-pair swapping history minimizes accumulated dephasing. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Linarith

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

private def bellman (v : List ℕ → ℕ) (x : List ℕ) : ℕ :=
  if h : 1 < x.length then
    (Finset.range (x.length - 1)).inf'
      ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun i => swapCost x i + v (merge x i))
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

private theorem merge_length (x : List ℕ) (i : ℕ) (h : i + 1 < x.length) :
    (merge x i).length + 1 = x.length := by
  sorry

private theorem maximum_merge (x : List ℕ) (i : ℕ) (h : i + 1 < x.length) :
    (merge x i).foldr max 0 = x.foldr max 0 := by
  sorry

private theorem potential_eq_boundary (x : List ℕ) :
    potential x = boundary (x.foldr max 0) x := by
  sorry

private theorem boundary_step_le (p : ℕ) (x : List ℕ) (i : ℕ)
    (h : i + 1 < x.length) :
    boundary p x ≤ (swapCost x i : ℤ) + boundary p (merge x i) := by
  sorry

private theorem boundary_step_eq (p : ℕ) (x : List ℕ) (i : ℕ)
    (h : i + 1 < x.length)
    (hg : ∀ j, j + 1 < (p :: x).length →
      max (x[i]?.getD 0) (x[i + 1]?.getD 0) ≤
        max ((p :: x)[j]?.getD 0) ((p :: x)[j + 1]?.getD 0)) :
    boundary p x = (swapCost x i : ℤ) + boundary p (merge x i) := by
  sorry

private theorem potential_step_le (x : List ℕ) (i : ℕ) (h : i + 1 < x.length) :
    potential x ≤ (swapCost x i : ℤ) + potential (merge x i) := by
  sorry

private theorem potential_step_eq (x : List ℕ) (i : ℕ) (h : IsGreedyStep x i) :
    potential x = (swapCost x i : ℤ) + potential (merge x i) := by
  sorry

private theorem greedy_exists (x : List ℕ) (h : 1 < x.length) :
    ∃ i, IsGreedyStep x i := by
  sorry

private theorem potential_terminal (x : List ℕ) (h : x.length ≤ 1) :
    potential x = 0 := by
  sorry

private theorem bellman_potential (n : ℕ) (x : List ℕ) (h : x.length ≤ n) :
    (((bellman^[n]) (fun _ => 0)) x : ℤ) = potential x := by
  sorry

private theorem dstar_potential (x : List ℕ) : (dstar x : ℤ) = potential x := by
  exact bellman_potential x.length x le_rfl

private theorem greedy_cost_potential (x : List ℕ) (hs : List ℕ)
    (h : IsGreedyRun x hs) : (runCost x hs : ℤ) = potential x := by
  sorry

/-- The earliest-pair conjecture (41), for every number of segments and every tie choice. -/
theorem result : claim := by
  intro x hs h
  exact_mod_cast (greedy_cost_potential x hs h).trans (dstar_potential x).symm

end D5.S3.Quantum.Optimization.SwapEarliestDephasingOptimality
