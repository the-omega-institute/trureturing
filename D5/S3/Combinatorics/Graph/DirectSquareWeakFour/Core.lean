/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Core
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Actual distances and landmark separation in complete graph direct squares. -/

import D5.S3.Combinatorics.Graph.HammingWeakTwoMetricDimensionCore
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset

variable {n : ℕ}

/-- The direct product of two complete graphs: both coordinates change along an edge. -/
def graph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj x y := x.1 ≠ y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A computable coordinate expression for the distance, justified below. -/
def coordDist {α β : Type*} [DecidableEq α] [DecidableEq β] (x y : α × β) : ℕ :=
  if x = y then 0 else if x.1 ≠ y.1 ∧ x.2 ≠ y.2 then 1 else 2

private theorem third (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  have hc : ({a,b} : Finset (Fin n)).card < (univ : Finset (Fin n)).card := by
    have : ({a,b} : Finset (Fin n)).card ≤ 2 := card_le_two
    simpa using (show ({a,b} : Finset (Fin n)).card < n by omega)
  obtain ⟨c, _, hc⟩ := exists_mem_notMem_of_card_lt_card hc
  exact ⟨c, by simpa using hc⟩

private theorem edist_formula (hn : 3 ≤ n) (x y : Fin n × Fin n) :
    (graph n).edist x y = coordDist x y := by
  by_cases hxy : x = y
  · simp [hxy, coordDist]
  by_cases hadj : x.1 ≠ y.1 ∧ x.2 ≠ y.2
  · simpa [coordDist, hxy, hadj] using
      (SimpleGraph.edist_eq_one_iff_adj.mpr hadj : (graph n).edist x y = 1)
  · have he : (graph n).edist x y = 2 := by
      apply SimpleGraph.edist_eq_two_iff.mpr
      refine ⟨hxy, hadj, ?_⟩
      obtain ⟨a, ha, ha'⟩ := third hn x.1 y.1
      obtain ⟨b, hb, hb'⟩ := third hn x.2 y.2
      exact ⟨(a,b), ⟨ha.symm, hb.symm⟩, ⟨ha'.symm, hb'.symm⟩⟩
    simpa [coordDist, hxy, hadj] using he

/-- The coordinate expression is the actual shortest-walk distance. -/
theorem distance_formula (hn : 3 ≤ n) (x y : Fin n × Fin n) :
    (graph n).dist x y = coordDist x y := by
  rw [SimpleGraph.dist, edist_formula hn]
  simp

/-- No junk distance is used: the actual graph is connected. -/
theorem connected (hn : 3 ≤ n) : (graph n).Connected := by
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  apply SimpleGraph.Connected.mk
  intro x y
  apply SimpleGraph.reachable_of_edist_ne_top
  rw [edist_formula hn]
  exact ENat.natCast_ne_top _

/-- Separation uses the actual graph metric and natural absolute difference. -/
noncomputable def delta (S : Finset (Fin n × Fin n)) (x y : Fin n × Fin n) : ℕ :=
  ∑ w ∈ S, Nat.dist ((graph n).dist x w) ((graph n).dist y w)

/-- Every distinct pair of actual graph vertices has separation at least four. -/
def IsWeakFour (S : Finset (Fin n × Fin n)) : Prop :=
  ∀ x y, x ≠ y → 4 ≤ delta S x y

/-- The least feasible landmark cardinality. Feasibility and attainment are proved in `Exact`. -/
noncomputable def wdim (n : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ S : Finset (Fin n × Fin n), IsWeakFour S ∧ S.card = c}

abbrev rowDegree := @HammingWeakTwoMetricDimension.rowDegree
abbrev colDegree := @HammingWeakTwoMetricDimension.colDegree

private theorem sum_endpoint (S : Finset (Fin n × Fin n)) (x : Fin n × Fin n) :
    (∑ w ∈ S, if w = x then 1 else 0) = if x ∈ S then 1 else 0 := by
  simp

/-- Proposition 2.2's shared-row identity, derived from actual shortest distances. -/
theorem delta_same_row (hn : 3 ≤ n) (S : Finset (Fin n × Fin n)) (i : Fin n)
    (j j' : Fin n) (h : j ≠ j') :
    delta S (i,j) (i,j') = colDegree S j + colDegree S j' +
      (if (i,j) ∈ S then 1 else 0) + (if (i,j') ∈ S then 1 else 0) := by
  have pointwise (w : Fin n × Fin n) :
      Nat.dist (coordDist (i,j) w) (coordDist (i,j') w) =
        (if w.2 = j then 1 else 0) + (if w.2 = j' then 1 else 0) +
        (if w = (i,j) then 1 else 0) + (if w = (i,j') then 1 else 0) := by
    by_cases hi : w.1 = i <;> by_cases hj : w.2 = j <;>
      by_cases hj' : w.2 = j' <;> simp_all [coordDist, Nat.dist, Prod.ext_iff, eq_comm]
  simp_rw [delta, distance_formula hn, pointwise, sum_add_distrib, sum_endpoint]
  simp only [sum_boole]
  rfl

/-- The transposed shared-column identity. -/
theorem delta_same_col (hn : 3 ≤ n) (S : Finset (Fin n × Fin n)) (i i' : Fin n)
    (j : Fin n) (h : i ≠ i') :
    delta S (i,j) (i',j) = rowDegree S i + rowDegree S i' +
      (if (i,j) ∈ S then 1 else 0) + (if (i',j) ∈ S then 1 else 0) := by
  have pointwise (w : Fin n × Fin n) :
      Nat.dist (coordDist (i,j) w) (coordDist (i',j) w) =
        (if w.1 = i then 1 else 0) + (if w.1 = i' then 1 else 0) +
        (if w = (i,j) then 1 else 0) + (if w = (i',j) then 1 else 0) := by
    by_cases hj : w.2 = j <;> by_cases hi : w.1 = i <;>
      by_cases hi' : w.1 = i' <;> simp_all [coordDist, Nat.dist, Prod.ext_iff, eq_comm]
  simp_rw [delta, distance_formula hn, pointwise, sum_add_distrib, sum_endpoint]
  simp only [sum_boole]
  rfl

/-- The four corner corrections in the direct-product rectangle identity. -/
theorem delta_rectangle (hn : 3 ≤ n) (S : Finset (Fin n × Fin n))
    (i i' j j' : Fin n) (hi : i ≠ i') (hj : j ≠ j') :
    delta S (i,j) (i',j') + (if (i,j) ∈ S then 1 else 0) +
      (if (i',j') ∈ S then 1 else 0) + 2 * (if (i,j') ∈ S then 1 else 0) +
      2 * (if (i',j) ∈ S then 1 else 0) =
      rowDegree S i + rowDegree S i' + colDegree S j + colDegree S j' := by
  have pointwise (w : Fin n × Fin n) :
      Nat.dist (coordDist (i,j) w) (coordDist (i',j') w) +
        (if w = (i,j) then 1 else 0) + (if w = (i',j') then 1 else 0) +
        2 * (if w = (i,j') then 1 else 0) + 2 * (if w = (i',j) then 1 else 0) =
        (if w.1 = i then 1 else 0) + (if w.1 = i' then 1 else 0) +
        (if w.2 = j then 1 else 0) + (if w.2 = j' then 1 else 0) := by
    by_cases hwi : w.1 = i <;> by_cases hwi' : w.1 = i' <;>
      by_cases hwj : w.2 = j <;> by_cases hwj' : w.2 = j' <;>
      simp_all [coordDist, Prod.ext_iff, Nat.dist, eq_comm]
  have hh := sum_congr (s₁ := S) (s₂ := S) rfl (fun w _ => pointwise w)
  simp only [sum_add_distrib, ← mul_sum] at hh
  simp only [sum_boole] at hh
  simp only [Nat.cast_id, filter_eq', apply_ite card, card_singleton, card_empty] at hh
  simpa only [delta, distance_formula hn, HammingWeakTwoMetricDimension.rowDegree,
    HammingWeakTwoMetricDimension.colDegree] using hh

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour
