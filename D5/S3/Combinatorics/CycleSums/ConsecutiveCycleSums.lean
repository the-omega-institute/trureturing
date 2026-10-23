/- GID: D5/S3/Combinatorics/CycleSums/ConsecutiveCycleSums
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CycleSums/ConsecutiveCycleSums
   mirror-E: none(waiver:elementary-cycle-completion)
   anchors: []
   utility: none
   digest: Star cores and tail prefixes complete cycles with sublinear added edges. -/

import D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsArithmetic
import D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSumsGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSums

open ConsecutiveCycleSumsArithmetic ConsecutiveCycleSumsGraph

/-- Vertex `v : Fin n` carries the label `v.val + 1`. -/
def label {n : ℕ} (v : Fin n) : ℕ := v.val + 1

/-- Every integer `1 ≤ k ≤ n(n+1)/2` is the label sum of a nonempty vertex set inducing a
connected subgraph of `G`. -/
def IsComplete {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n * (n + 1) / 2 →
    ∃ C : Finset (Fin n), C.Nonempty ∧ (G.induce (C : Set (Fin n))).Connected ∧ ∑ v ∈ C, label v = k

/-- Marotti–Needleman §5: for every a ≥ 1, eventually at most n/a added edges complete the n-cycle. -/
def claim : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ G : SimpleGraph (Fin n), SimpleGraph.cycleGraph n ≤ G ∧
      (G.edgeSet \ (SimpleGraph.cycleGraph n).edgeSet).ncard * a ≤ n ∧ IsComplete G

private theorem hub_tail_sum {n k j s : ℕ} (hn : 0 < n) (hk4 : 4 ≤ k) (hk : k < n)
    (hj : k ≤ j) (hjn : j ≤ n) (hs : 2 ≤ s) (hst : s + 3 ≤ tri k) :
    ∃ C : Finset (Fin n), C.Nonempty ∧
      ((completion n k hn).induce (C : Set (Fin n))).Connected ∧
      ∑ v ∈ C, label v = 1 + s + tail k j := by
  classical
  obtain ⟨S, hS, hsum⟩ := subset_sums hk4 hs hst
  let A := insert 1 (S ∪ Finset.Icc (k + 1) j)
  have hA : ∀ x ∈ A, 1 ≤ x ∧ x ≤ n := by
    intro x hx
    simp only [A, Finset.mem_insert, Finset.mem_union, Finset.mem_Icc] at hx
    rcases hx with rfl | hx | hx
    · omega
    · have := hS _ hx
      omega
    · omega
  have hnot : 1 ∉ S ∪ Finset.Icc (k + 1) j := by
    simp only [Finset.mem_union, Finset.mem_Icc, not_or]
    constructor
    · intro h
      have := hS _ h
      omega
    · omega
  have hdis : Disjoint S (Finset.Icc (k + 1) j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hh
    have := hS _ hx
    simp only [Finset.mem_Icc] at hh
    omega
  refine ⟨vertices n A, ⟨⟨0, hn⟩, by simp [A]⟩,
    hub_tail_connected hn hk hj hjn S hS, ?_⟩
  change (∑ v ∈ vertices n A, (v.val + 1)) = _
  rw [sum_vertices hA]
  dsimp [A]
  rw [Finset.sum_insert hnot, Finset.sum_union hdis, hsum]
  simp only [tail, Nat.add_assoc]

private theorem middle_sum {n k q : ℕ} (hn : 0 < n) (hk4 : 4 ≤ k)
    (hk : k < n) (ht : n + 4 ≤ tri k) (hq : 3 ≤ q) (hqt : q + 2 ≤ tri n) :
    ∃ C : Finset (Fin n), C.Nonempty ∧
      ((completion n k hn).induce (C : Set (Fin n))).Connected ∧
      ∑ v ∈ C, label v = q := by
  obtain ⟨j, hkj, hjn, hlo, hhi⟩ := interval_cover (by omega) ht hq hqt
  have hs : 2 ≤ q - tail k j - 1 := by omega
  have hst : q - tail k j - 1 + 3 ≤ tri k := by omega
  obtain ⟨C, hC, hc, hsum⟩ := hub_tail_sum hn hk4 hk hkj hjn hs hst
  refine ⟨C, hC, hc, ?_⟩
  rw [hsum]
  omega

private theorem interval_sum {n k l j : ℕ} (hn : 0 < n)
    (hl : 1 ≤ l) (hlj : l ≤ j) (hjn : j ≤ n) :
    ∃ C : Finset (Fin n), C.Nonempty ∧
      ((completion n k hn).induce (C : Set (Fin n))).Connected ∧
      ∑ v ∈ C, label v = ∑ x ∈ Finset.Icc l j, x := by
  let v : Fin n := ⟨l - 1, by omega⟩
  refine ⟨vertices n (Finset.Icc l j), ⟨v, ?_⟩,
    interval_connected hn hl hlj hjn, ?_⟩
  · apply mem_vertices.mpr
    simp only [Finset.mem_Icc]
    dsimp [v]
    omega
  · apply sum_vertices
    intro x hx
    simp only [Finset.mem_Icc] at hx
    omega

private theorem completion_complete {n k : ℕ} (hn8 : 8 ≤ n) (hk4 : 4 ≤ k)
    (hk : k < n) (ht : n + 4 ≤ tri k) :
    IsComplete (completion n k (by omega)) := by
  intro q hq hqt
  have hn : 0 < n := by omega
  change q ≤ tri n at hqt
  by_cases hq1 : q = 1
  · subst q
    simpa using (interval_sum (k := k) hn (l := 1) (j := 1) (by omega) (by omega) (by omega))
  by_cases hq2 : q = 2
  · subst q
    simpa using (interval_sum (k := k) hn (l := 2) (j := 2) (by omega) (by omega) (by omega))
  by_cases hqm : q + 2 ≤ tri n
  · exact middle_sum hn hk4 hk ht (by omega) hqm
  by_cases hqtop : q = tri n
  · subst q
    simpa only [sum_Icc_one n] using
      (interval_sum (k := k) hn (l := 1) (j := n) (by omega) (by omega) (by omega))
  · have heq : q = tri n - 1 := by omega
    rw [heq]
    simpa only [sum_Icc_two (show 1 ≤ n by omega)] using
      (interval_sum (k := k) hn (l := 2) (j := n) (by omega) (by omega) (by omega))

private theorem strong_completion {n : ℕ} (hn : 8 ≤ n) :
    ∃ (k : ℕ) (G : SimpleGraph (Fin n)),
      SimpleGraph.cycleGraph n ≤ G ∧
      (G.edgeSet \ (SimpleGraph.cycleGraph n).edgeSet).ncard ≤ k - 1 ∧
      (k - 1) ^ 2 < 2 * n + 8 ∧ IsComplete G := by
  obtain ⟨k, hk4, hkn, ht, hsq⟩ := choose_core hn
  refine ⟨k, completion n k (by omega), cycle_le_completion _ _ _,
    added_edges_le _, hsq, completion_complete hn hk4 hkn ht⟩

/-- A square-root bound on the explicit completion gives the eventual linear-fraction bound. -/
theorem result : claim := by
  intro a ha
  refine ⟨max 8 (4 * a ^ 2), ?_⟩
  intro n hn
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
  have hna : 4 * a ^ 2 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨k, G, hcycle, hedge, hsq, hcomplete⟩ := strong_completion hn8
  refine ⟨G, hcycle, ?_, hcomplete⟩
  have hbound : (k - 1) * a ≤ n := by
    by_contra hbad
    have hbad : n < (k - 1) * a := by omega
    have hsqa := Nat.mul_lt_mul_of_pos_right hsq (show 0 < a ^ 2 by positivity)
    have hn2 : n ^ 2 < ((k - 1) * a) ^ 2 := by nlinarith
    have hfactor : ((k - 1) * a) ^ 2 = (k - 1) ^ 2 * a ^ 2 := by ring
    have hbig : 3 * a ^ 2 ≤ n := by omega
    have h8 : 2 * n + 8 ≤ 3 * n := by omega
    nlinarith
  exact (Nat.mul_le_mul_right a hedge).trans hbound

end D5.S3.Combinatorics.CycleSums.ConsecutiveCycleSums
