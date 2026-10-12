/- GID: D5/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HammingWeakTwoMetricDimensionCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hamming distance separation is characterized by row and column landmark degrees. -/

import Mathlib.Data.Nat.Dist
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension

open Finset

variable {n m : ℕ}

/-- Hamming distance on the Cartesian product of two complete graphs. -/
def dist (x y : Fin n × Fin m) : ℕ :=
  (if x.1 ≠ y.1 then 1 else 0) + (if x.2 ≠ y.2 then 1 else 0)

/-- Sum of the absolute differences of the distances to the landmarks. -/
def delta (S : Finset (Fin n × Fin m)) (x y : Fin n × Fin m) : ℕ :=
  ∑ w ∈ S, Nat.dist (dist x w) (dist y w)

/-- Every distinct pair has separation at least `k`. -/
def IsWeakResolving (k : ℕ) (S : Finset (Fin n × Fin m)) : Prop :=
  ∀ x y : Fin n × Fin m, x ≠ y → k ≤ delta S x y

/-- The least achievable cardinality; the infimum of an empty set is zero. -/
noncomputable def wdim (n m k : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ S : Finset (Fin n × Fin m), IsWeakResolving k S ∧ S.card = c}

/-- Number of landmarks in a row. -/
def rowDegree (S : Finset (Fin n × Fin m)) (i : Fin n) : ℕ :=
  (S.filter (fun w => w.1 = i)).card

/-- Number of landmarks in a column. -/
def colDegree (S : Finset (Fin n × Fin m)) (j : Fin m) : ℕ :=
  (S.filter (fun w => w.2 = j)).card

theorem sum_rowDegree (S : Finset (Fin n × Fin m)) :
    (∑ i, rowDegree S i) = S.card := by
  simpa [rowDegree] using (card_eq_sum_card_fiberwise (s := S)
    (t := univ) (f := Prod.fst) (fun _ _ => mem_univ _)).symm

theorem sum_colDegree (S : Finset (Fin n × Fin m)) :
    (∑ j, colDegree S j) = S.card := by
  simpa [colDegree] using (card_eq_sum_card_fiberwise (s := S)
    (t := univ) (f := Prod.snd) (fun _ _ => mem_univ _)).symm

/-- A pair in one row is separated by the sum of its two column degrees. -/
theorem delta_same_row (S : Finset (Fin n × Fin m)) (i : Fin n)
    (j j' : Fin m) (h : j ≠ j') :
    delta S (i,j) (i,j') = colDegree S j + colDegree S j' := by
  have pointwise (w : Fin n × Fin m) :
      Nat.dist (dist (i,j) w) (dist (i,j') w) =
        (if w.2 = j then 1 else 0) + (if w.2 = j' then 1 else 0) := by
    by_cases hi : i = w.1 <;> by_cases hj : w.2 = j <;>
      by_cases hj' : w.2 = j' <;> simp_all [dist, Nat.dist, eq_comm]
  simp_rw [delta, pointwise, sum_add_distrib, sum_boole]
  rfl

/-- A pair in one column is separated by the sum of its two row degrees. -/
theorem delta_same_col (S : Finset (Fin n × Fin m)) (i i' : Fin n)
    (j : Fin m) (h : i ≠ i') :
    delta S (i,j) (i',j) = rowDegree S i + rowDegree S i' := by
  have pointwise (w : Fin n × Fin m) :
      Nat.dist (dist (i,j) w) (dist (i',j) w) =
        (if w.1 = i then 1 else 0) + (if w.1 = i' then 1 else 0) := by
    by_cases hj : j = w.2 <;> by_cases hi : w.1 = i <;>
      by_cases hi' : w.1 = i' <;> simp_all [dist, Nat.dist, eq_comm]
  simp_rw [delta, pointwise, sum_add_distrib, sum_boole]
  rfl

/-- For a rectangle, the two opposite landmark corners subtract two each. -/
theorem delta_rectangle (S : Finset (Fin n × Fin m))
    (i i' : Fin n) (j j' : Fin m) (hi : i ≠ i') (hj : j ≠ j') :
    delta S (i,j) (i',j') + 2 * (if (i,j') ∈ S then 1 else 0) +
      2 * (if (i',j) ∈ S then 1 else 0) =
      rowDegree S i + rowDegree S i' + colDegree S j + colDegree S j' := by
  have pointwise (w : Fin n × Fin m) :
      Nat.dist (dist (i,j) w) (dist (i',j') w) +
        2 * (if w = (i,j') then 1 else 0) +
        2 * (if w = (i',j) then 1 else 0) =
        (if w.1 = i then 1 else 0) + (if w.1 = i' then 1 else 0) +
        (if w.2 = j then 1 else 0) + (if w.2 = j' then 1 else 0) := by
    by_cases hwi : w.1 = i <;> by_cases hwi' : w.1 = i' <;>
      by_cases hwj : w.2 = j <;> by_cases hwj' : w.2 = j' <;>
      simp_all [dist, Prod.ext_iff, Nat.dist, eq_comm]
  have hh := sum_congr (s₁ := S) (s₂ := S) rfl (fun w _ => pointwise w)
  simp only [sum_add_distrib, ← mul_sum, sum_boole] at hh
  by_cases ha : (i,j') ∈ S <;> by_cases hb : (i',j) ∈ S <;>
    simpa [delta, rowDegree, colDegree, filter_eq', ha, hb, eq_comm] using hh

theorem row_pair_degree (S : Finset (Fin n × Fin m))
    (hS : IsWeakResolving 2 S) (i i' : Fin n) (j : Fin m) (hi : i ≠ i') :
    2 ≤ rowDegree S i + rowDegree S i' := by
  have h := hS (i,j) (i',j) (by simpa using hi)
  rwa [delta_same_col S i i' j hi] at h

theorem col_pair_degree (S : Finset (Fin n × Fin m))
    (hS : IsWeakResolving 2 S) (i : Fin n) (j j' : Fin m) (hj : j ≠ j') :
    2 ≤ colDegree S j + colDegree S j' := by
  have h := hS (i,j) (i,j') (by simpa using hj)
  rwa [delta_same_row S i j j' hj] at h

theorem disjoint_landmark_degree (S : Finset (Fin n × Fin m))
    (hS : IsWeakResolving 2 S) (i i' : Fin n) (j j' : Fin m)
    (hij : (i,j) ∈ S) (hij' : (i',j') ∈ S) (hi : i ≠ i') (hj : j ≠ j') :
    6 ≤ rowDegree S i + colDegree S j + rowDegree S i' + colDegree S j' := by
  have hd := delta_rectangle S i i' j' j hi (Ne.symm hj)
  have hw := hS (i,j') (i',j) (by intro h; exact hi (congrArg Prod.fst h))
  simp only [if_pos hij, if_pos hij', mul_one] at hd
  omega

/-- The row, column and disjoint-edge conditions suffice, including empty rows. -/
theorem weak_of_pair_degrees (S : Finset (Fin n × Fin m))
    (hr : ∀ i i', i ≠ i' → 2 ≤ rowDegree S i + rowDegree S i')
    (hc : ∀ j j', j ≠ j' → 2 ≤ colDegree S j + colDegree S j')
    (he : ∀ i i' j j', (i,j) ∈ S → (i',j') ∈ S → i ≠ i' → j ≠ j' →
      6 ≤ rowDegree S i + colDegree S j + rowDegree S i' + colDegree S j') :
    IsWeakResolving 2 S := by
  intro x y hxy
  rcases x with ⟨i,j⟩
  rcases y with ⟨i',j'⟩
  by_cases hi : i = i'
  · subst i'
    have hj : j ≠ j' := by simpa using hxy
    rw [delta_same_row S i j j' hj]
    exact hc j j' hj
  by_cases hj : j = j'
  · subst j'
    rw [delta_same_col S i i' j hi]
    exact hr i i' hi
  have hd := delta_rectangle S i i' j j' hi hj
  have hrow := hr i i' hi
  have hcol := hc j j' hj
  by_cases ha : (i,j') ∈ S <;> by_cases hb : (i',j) ∈ S
  · have hh := he i i' j' j ha hb hi (Ne.symm hj)
    simp only [if_pos ha, if_pos hb, mul_one] at hd
    omega
  · simp only [if_pos ha, if_neg hb, mul_one, mul_zero, add_zero] at hd
    omega
  · simp only [if_neg ha, if_pos hb, mul_one, mul_zero, add_zero] at hd
    omega
  · simp only [if_neg ha, if_neg hb, mul_zero, add_zero] at hd
    omega

/-- Nonempty rows and columns with edge endpoint-degree sums at least three suffice. -/
theorem weak_of_degrees (S : Finset (Fin n × Fin m))
    (hr : ∀ i, 1 ≤ rowDegree S i) (hc : ∀ j, 1 ≤ colDegree S j)
    (he : ∀ i j, (i,j) ∈ S → 3 ≤ rowDegree S i + colDegree S j) :
    IsWeakResolving 2 S := by
  apply weak_of_pair_degrees S
  · intro i i' _
    have := hr i
    have := hr i'
    omega
  · intro j j' _
    have := hc j
    have := hc j'
    omega
  · intro i i' j j' ha hb _ _
    have := he i j ha
    have := he i' j' hb
    omega

/-- The entire product always resolves distinct vertices with separation at least two. -/
theorem univ_weak_two (n m : ℕ) :
    IsWeakResolving 2 (univ : Finset (Fin n × Fin m)) := by
  intro x y hxy
  have hpos : 1 ≤ dist x y := by
    by_cases hi : x.1 = y.1 <;> by_cases hj : x.2 = y.2 <;>
      simp_all [dist, Prod.ext_iff]
  have hsym : dist y x = dist x y := by simp [dist, ne_comm]
  have hpair := sum_le_sum_of_subset (f := fun w => Nat.dist (dist x w) (dist y w))
    (show ({x,y} : Finset (Fin n × Fin m)) ⊆ univ by simp)
  have hx : dist x x = 0 := by simp [dist]
  have hy : dist y y = 0 := by simp [dist]
  simp only [sum_pair hxy, hx, hy, hsym, Nat.dist_zero_right,
    Nat.dist_zero_left] at hpair
  change 2 ≤ ∑ w ∈ univ, Nat.dist (dist x w) (dist y w)
  omega

theorem wdim_le_card (S : Finset (Fin n × Fin m)) (k : ℕ)
    (hS : IsWeakResolving k S) : wdim n m k ≤ S.card := by
  exact csInf_le' ⟨S, hS, rfl⟩

theorem le_wdim_two (a : ℕ)
    (h : ∀ S : Finset (Fin n × Fin m), IsWeakResolving 2 S → a ≤ S.card) :
    a ≤ wdim n m 2 := by
  apply le_csInf
  · exact ⟨_, univ, univ_weak_two n m, rfl⟩
  · rintro c ⟨S, hS, rfl⟩
    exact h S hS

end D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimension
