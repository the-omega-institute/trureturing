/- GID: D5/S3/Combinatorics/Graph/StarForming/WeightedBalance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/WeightedBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Actual symmetric neighbor sums annihilate selected balance equations. -/

import D5.S3.Combinatorics.Graph.StarForming.DegreeCapacity

/-! The weighted summation argument of CUBIC_EQUALITY_PADDING_RINGS,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0.
All neighbor and selected-degree sums below use the actual graph. -/
namespace D5.S3.Combinatorics.Graph.StarForming.WeightedBalance
open scoped BigOperators
open DegreeCapacity
variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborSum (weight : V → ℤ) (v : V) : ℤ :=
  ∑ w : V, if G.Adj v w then weight w else 0

/-- Interchanging actual adjacency sums transports an eigenvector identity
to the balance equation of every finite selected set. -/
theorem annihilate (weight : V → ℤ) (c : ℤ)
    (hweight : ∀ v, neighborSum G weight v + c * weight v = 0)
    (D : Finset V) :
    ∑ v : V, weight v * ((selectedDegree G D v : ℤ) +
      c * (if v ∈ D then 1 else 0)) = 0 := by
  classical
  have hs (v : V) : (selectedDegree G D v : ℤ) =
      ∑ w ∈ D, if G.Adj v w then (1 : ℤ) else 0 := by
    simp [selectedDegree]
  simp_rw [hs, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have he : (∑ w ∈ D, ∑ v : V, weight v * (if G.Adj v w then (1 : ℤ) else 0)) =
      ∑ w ∈ D, neighborSum G weight w := by
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : G.Adj v w <;> simp [neighborSum, G.adj_comm, h]
  rw [he]
  have ht : (∑ v : V, weight v * (c * (if v ∈ D then 1 else 0))) =
      ∑ v ∈ D, c * weight v := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [ht, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun v _ => hweight v)

end D5.S3.Combinatorics.Graph.StarForming.WeightedBalance
