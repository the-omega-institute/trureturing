/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.DegreeSum]
   utility: none
   digest: Low-degree boundary charging in finite simple graphs. -/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors retained in a specified vertex set. -/
def neighborsIn (A : Finset V) (v : V) : Finset V := A.filter (G.Adj v)

omit [Fintype V] [DecidableEq V] in
/-- Counting an oriented cut in the two orders, with arbitrary vertex weights. -/
theorem sum_neighborsIn (A B : Finset V) (f : V → ℕ) :
    (∑ v ∈ A, ∑ w ∈ neighborsIn G B v, f w) =
      ∑ w ∈ B, (neighborsIn G A w).card * f w := by
  simp_rw [neighborsIn, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  simp_rw [G.adj_comm]
  rw [← sum_filter]
  simp

/-- In a finite graph, low vertices with no two adjacent internal degree-two
vertices use at most three vertices per two edges leaving the low set. -/
theorem low_boundary_bound (L : Finset V)
    (hdeg : ∀ v ∈ L, G.degree v = 2)
    (hmid : ∀ v ∈ L, ∀ w ∈ L, G.Adj v w →
      (neighborsIn G L v).card = 2 → (neighborsIn G L w).card ≤ 1) :
    2 * L.card ≤ 3 * ∑ v ∈ L, (neighborsIn G (univ \ L) v).card := by
  let d (v : V) := (neighborsIn G L v).card
  let b (v : V) := (neighborsIn G (univ \ L) v).card
  have split (v : V) : d v + b v = G.degree v := by
    have h := card_filter_add_card_filter_not (s := G.neighborFinset v) (fun w => w ∈ L)
    have hL : (G.neighborFinset v).filter (fun w => w ∈ L) = neighborsIn G L v := by
      ext w; simp [neighborsIn, and_comm]
    have hB : (G.neighborFinset v).filter (fun w => w ∉ L) =
        neighborsIn G (univ \ L) v := by
      ext w; simp [neighborsIn, and_comm]
    rw [hL, hB] at h
    exact h
  have local_bound (v : V) (hv : v ∈ L) :
      2 + d v * b v ≤ 3 * b v + ∑ w ∈ neighborsIn G L v, b w := by
    have hs := split v
    rw [hdeg v hv] at hs
    by_cases hd : d v = 2
    · have hb : b v = 0 := by omega
      have hsum : d v ≤ ∑ w ∈ neighborsIn G L v, b w := by
        calc
          d v = ∑ _w ∈ neighborsIn G L v, 1 := by simp [d]
          _ ≤ _ := by
            apply sum_le_sum
            intro w hw
            obtain ⟨hwL, hww⟩ := mem_filter.mp hw
            have hm := hmid v hv w hwL hww hd
            have hsw := split w
            rw [hdeg w hwL] at hsw
            change d w ≤ 1 at hm
            omega
      simpa [hd, hb] using hsum
    · have : d v ≤ 1 := by omega
      have : 2 + d v * b v ≤ 3 * b v := by
        interval_cases h : d v <;> simp_all <;> omega
      exact this.trans (Nat.le_add_right _ _)
  have total := sum_le_sum local_bound
  have swap := sum_neighborsIn G L L b
  change (∑ v ∈ L, ∑ w ∈ neighborsIn G L v, b w) =
    ∑ w ∈ L, d w * b w at swap
  simp only [sum_add_distrib, sum_const, smul_eq_mul, ← mul_sum, swap] at total
  change 2 * L.card ≤ 3 * ∑ v ∈ L, b v
  omega

/-- The boundary entering the complementary set is bounded by its total degree. -/
theorem boundary_le_degree (L : Finset V) :
    (∑ v ∈ L, (neighborsIn G (univ \ L) v).card) ≤
      ∑ w ∈ univ \ L, G.degree w := by
  have hs := sum_neighborsIn G L (univ \ L) (fun _ => 1)
  simp only [sum_const, smul_eq_mul, mul_one] at hs
  rw [hs]
  apply sum_le_sum
  intro w _
  exact card_le_card (show neighborsIn G L w ⊆ G.neighborFinset w by
    intro v hv
    exact (G.mem_neighborFinset _ _).mpr (mem_filter.mp hv).2)

/-- A minimum-degree-two graph satisfying the local low-path obstruction has
at least twelve elevenths as many edges as vertices. -/
theorem excess_bound (hmin : ∀ v, 2 ≤ G.degree v)
    (hmid : ∀ v w, G.degree v = 2 → G.degree w = 2 → G.Adj v w →
      (neighborsIn G (univ.filter (fun u => G.degree u = 2)) v).card = 2 →
      (neighborsIn G (univ.filter (fun u => G.degree u = 2)) w).card ≤ 1) :
    12 * Fintype.card V ≤ 11 * G.edgeFinset.card := by
  let L := univ.filter (fun v => G.degree v = 2)
  let H := univ \ L
  have hl (v : V) (hv : v ∈ L) : G.degree v = 2 := (mem_filter.mp hv).2
  have hh (v : V) (hv : v ∈ H) : 3 ≤ G.degree v := by
    have hnot : G.degree v ≠ 2 := by simpa [H, L] using hv
    have := hmin v
    omega
  have count : L.card + H.card = Fintype.card V := by
    have := card_sdiff_add_card_eq_card (show L ⊆ univ from subset_univ _)
    simpa [H, add_comm] using this
  have sumL : (∑ v ∈ L, G.degree v) = 2 * L.card := by
    calc
      _ = ∑ _v ∈ L, 2 := sum_congr rfl hl
      _ = _ := by simp [mul_comm]
  have sumH : 3 * H.card ≤ ∑ v ∈ H, G.degree v := by
    have := sum_le_sum hh
    simpa [mul_comm] using this
  have sumAll : 2 * L.card + (∑ v ∈ H, G.degree v) = 2 * G.edgeFinset.card := by
    rw [← sumL, ← sum_union (disjoint_sdiff_self_right),
      union_sdiff_of_subset (subset_univ L)]
    exact G.sum_degrees_eq_twice_card_edges
  have bound := (low_boundary_bound G L hl
    (fun v hv w hw ha hd => hmid v w (hl v hv) (hl w hw) ha hd)).trans
      (Nat.mul_le_mul_left 3 (boundary_le_degree G L))
  change 2 * L.card ≤ 3 * ∑ v ∈ H, G.degree v at bound
  omega

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour
