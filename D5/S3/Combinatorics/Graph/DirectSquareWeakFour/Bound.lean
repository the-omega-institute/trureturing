/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The eleven-to-twenty-four universal lower estimate for direct-square landmarks. -/

import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Lower

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset

variable {n : ℕ}

/-- The two incidence parts count exactly twice the number of landmarks. -/
theorem incidence_edges (S : Finset (Fin n × Fin n)) :
    (incidence S).edgeFinset.card = S.card := by
  have hd := (incidence S).sum_degrees_eq_twice_card_edges
  have hs : (∑ v, (incidence S).degree v) = 2*S.card := by
    rw [Fintype.sum_sum_type]
    simp_rw [(incidence_degrees S).1, (incidence_degrees S).2]
    rw [HammingWeakTwoMetricDimension.sum_rowDegree,
      HammingWeakTwoMetricDimension.sum_colDegree]
    omega
  omega

theorem no_low_walk (hn : 4 ≤ n) (S : Finset (Fin n × Fin n)) (hS : IsWeakFour S)
    (a b c d : Fin n ⊕ Fin n)
    (hab : (incidence S).Adj a b) (hbc : (incidence S).Adj b c)
    (hcd : (incidence S).Adj c d) (hac : a ≠ c) (hbd : b ≠ d)
    (ha : (incidence S).degree a = 2) (hb : (incidence S).degree b = 2)
    (hc : (incidence S).degree c = 2) (hd : (incidence S).degree d = 2) : False := by
  rcases a with a|a <;> rcases b with b|b <;>
    rcases c with c|c <;> rcases d with d|d <;>
    simp only [incidence] at hab hbc hcd <;> try contradiction
  · exact no_low_rectangle_path hn S hS a c b d
      (by simpa using hac) (by simpa using hbd) hab hbc hcd
      (by simpa only [(incidence_degrees S).1] using ha)
      (by simpa only [(incidence_degrees S).1] using hc)
      (by simpa only [(incidence_degrees S).2] using hb)
      (by simpa only [(incidence_degrees S).2] using hd)
  · exact no_low_rectangle_path hn S hS d b c a
      (by simpa using (Ne.symm hbd)) (by simpa using (Ne.symm hac)) hcd hbc hab
      (by simpa only [(incidence_degrees S).1] using hd)
      (by simpa only [(incidence_degrees S).1] using hb)
      (by simpa only [(incidence_degrees S).2] using hc)
      (by simpa only [(incidence_degrees S).2] using ha)

/-- Adjacent low vertices cannot both have two low neighbors. -/
theorem low_middle (hn : 4 ≤ n) (S : Finset (Fin n × Fin n)) (hS : IsWeakFour S)
    (v w : Fin n ⊕ Fin n) (hv : (incidence S).degree v = 2)
    (hw : (incidence S).degree w = 2) (hadj : (incidence S).Adj v w)
    (hd : (neighborsIn (incidence S) (univ.filter (fun u => (incidence S).degree u = 2)) v).card
      = 2) :
    (neighborsIn (incidence S) (univ.filter (fun u => (incidence S).degree u = 2)) w).card ≤ 1 := by
  by_contra hh
  let L := univ.filter (fun u => (incidence S).degree u = 2)
  obtain ⟨a, ha, haw⟩ := exists_mem_ne (show 1 < (neighborsIn (incidence S) L v).card by
    change 1 < (neighborsIn (incidence S) (univ.filter _) v).card
    omega) w
  obtain ⟨b, hb, hbv⟩ := exists_mem_ne (show 1 < (neighborsIn (incidence S) L w).card by
    dsimp only [L]
    omega) v
  obtain ⟨haL,hva⟩ := mem_filter.mp ha
  obtain ⟨hbL,hwb⟩ := mem_filter.mp hb
  exact no_low_walk hn S hS a v w b hva.symm hadj hwb haw (Ne.symm hbv)
    (mem_filter.mp haL).2 hv hw (mem_filter.mp hbL).2

/-- Every minimum-degree-two weak-four set obeys the sharp linear estimate. -/
theorem linear_lower (hn : 4 ≤ n) (S : Finset (Fin n × Fin n)) (hS : IsWeakFour S)
    (hr : ∀ i, 2 ≤ rowDegree S i) (hc : ∀ j, 2 ≤ colDegree S j) :
    24*n ≤ 11*S.card := by
  have hmin : ∀ v, 2 ≤ (incidence S).degree v := by
    rintro (i|j)
    · simpa only [(incidence_degrees S).1] using hr i
    · simpa only [(incidence_degrees S).2] using hc j
  have h := excess_bound (incidence S) hmin (low_middle hn S hS)
  rw [incidence_edges] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour
