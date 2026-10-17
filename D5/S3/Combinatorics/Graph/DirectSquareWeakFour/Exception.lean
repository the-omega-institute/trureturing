/- GID: D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The five-by-five direct square requires twelve weak-four landmarks. -/

import D5.S3.Combinatorics.Graph.DirectSquareWeakFour.Bound

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DirectSquareWeakFour

open Finset

private theorem one_excess {n : ℕ} (f : Fin n → ℕ) (hmin : ∀ i, 2 ≤ f i)
    (hs : (∑ i, f i) = 2*n+1) :
    ∃ a, f a = 3 ∧ ∀ i, i ≠ a → f i = 2 := by
  have he : (∑ i, (f i - 2)) = 1 := by
    have hpoint (i : Fin n) : f i = (f i-2)+2 := by have := hmin i; omega
    have hh : (∑ i, f i) = (∑ i, (f i-2)) + n*2 := by
      calc
        _ = ∑ i, ((f i-2)+2) := sum_congr rfl (fun i _ => hpoint i)
        _ = _ := by simp [sum_add_distrib]
    omega
  obtain ⟨a, _, ha⟩ := sum_pos_iff.mp (show 0 < ∑ i, (f i-2) by omega)
  have hle : f a-2 ≤ 1 := by
    have := single_le_sum (f := fun i => f i-2) (fun i _ => Nat.zero_le _) (mem_univ a)
    omega
  have hfa : f a = 3 := by omega
  refine ⟨a, hfa, ?_⟩
  intro i hi
  have hp := sum_le_sum_of_subset (f := fun i => f i-2)
    (show ({a,i} : Finset (Fin n)) ⊆ univ from subset_univ _)
  rw [sum_pair (Ne.symm hi), he] at hp
  have := hmin i
  omega

private theorem no_low_cycle {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n × Fin n))
    (hS : IsWeakFour S) (v a u b : Fin n ⊕ Fin n)
    (hva : (incidence S).Adj v a) (hua : (incidence S).Adj u a)
    (hub : (incidence S).Adj u b) (hvb : (incidence S).Adj v b)
    (hvu : v ≠ u) (hab : a ≠ b)
    (hv : (incidence S).degree v = 2) (ha : (incidence S).degree a = 2)
    (hu : (incidence S).degree u = 3) (hb : (incidence S).degree b = 2) : False := by
  rcases v with v|v <;> rcases a with a|a <;>
    rcases u with u|u <;> rcases b with b|b <;>
    simp only [incidence] at hva hua hub hvb <;> try contradiction
  · have hrow : v ≠ u := by simpa using hvu
    have hcol : a ≠ b := by simpa using hab
    have hd := delta_rectangle (by omega) S v u a b hrow hcol
    have hw := hS (v,a) (u,b) (by intro h; exact hrow (congrArg Prod.fst h))
    simp only [(incidence_degrees S).1, (incidence_degrees S).2] at hv ha hu hb
    simp only [if_pos hva, if_pos hua, if_pos hub, if_pos hvb, hv, ha, hu, hb] at hd
    omega
  · have hrow : a ≠ b := by simpa using hab
    have hcol : v ≠ u := by simpa using hvu
    have hd := delta_rectangle (by omega) S a b v u hrow hcol
    have hw := hS (a,v) (b,u) (by intro h; exact hrow (congrArg Prod.fst h))
    simp only [(incidence_degrees S).1, (incidence_degrees S).2] at hv ha hu hb
    simp only [if_pos hva, if_pos hua, if_pos hub, if_pos hvb, hv, ha, hu, hb] at hd
    omega

/-- Eleven landmarks are impossible at order five, even though the linear bound allows them. -/
theorem five_obstruction (S : Finset (Fin 5 × Fin 5)) (hS : IsWeakFour S)
    (hc : S.card = 11) : False := by
  obtain ⟨hr,hcol⟩ := minimum_degrees (by omega) S hS (by omega)
  obtain ⟨A,hA,hrows⟩ := one_excess (rowDegree S) hr (by
    rw [HammingWeakTwoMetricDimension.sum_rowDegree]; omega)
  obtain ⟨C,hC,hcols⟩ := one_excess (colDegree S) hcol (by
    rw [HammingWeakTwoMetricDimension.sum_colDegree]; omega)
  let G := incidence S
  let L := univ.filter (fun v => G.degree v = 2)
  let H := univ \ L
  let high : Fin 5 ⊕ Fin 5 → Fin 5 ⊕ Fin 5 :=
    Sum.elim (fun _ => Sum.inl A) (fun _ => Sum.inr C)
  have unique (v a u : Fin 5 ⊕ Fin 5) (hva : G.Adj v a) (hau : G.Adj a u)
      (hu : G.degree u ≠ 2) : u = high v := by
    rcases v with v|v <;> rcases a with a|a <;> rcases u with u|u <;>
      simp only [G, incidence] at hva hau <;> try contradiction
    · have hu' : rowDegree S u ≠ 2 := by simpa only [G, (incidence_degrees S).1] using hu
      have he : u = A := by by_contra h; exact hu' (hrows u h)
      simp [high, he]
    · have hu' : colDegree S u ≠ 2 := by simpa only [G, (incidence_degrees S).2] using hu
      have he : u = C := by by_contra h; exact hu' (hcols u h)
      simp [high, he]
  have high_degree (v : Fin 5 ⊕ Fin 5) : G.degree (high v) = 3 := by
    rcases v with v|v
    · change (incidence S).degree (.inl A) = 3
      rw [(incidence_degrees S).1]
      exact hA
    · change (incidence S).degree (.inr C) = 3
      rw [(incidence_degrees S).2]
      exact hC
  have local_bound (v : Fin 5 ⊕ Fin 5) (hv : v ∈ L) :
      (neighborsIn G L v).card ≤ 1 := by
    have hdv : G.degree v = 2 := (mem_filter.mp hv).2
    by_contra hh
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (show 1 < (neighborsIn G L v).card by omega)
    obtain ⟨haL,hva⟩ := mem_filter.mp ha
    obtain ⟨hbL,hvb⟩ := mem_filter.mp hb
    have hda : G.degree a = 2 := (mem_filter.mp haL).2
    have hdb : G.degree b = 2 := (mem_filter.mp hbL).2
    have other (a b : Fin 5 ⊕ Fin 5) (ha : G.Adj v a) (hb : G.Adj v b)
        (hab : a ≠ b) (hda : G.degree a = 2) (hdb : G.degree b = 2) :
        G.Adj a (high v) ∧ high v ≠ v := by
      obtain ⟨u,hu,huv⟩ := exists_mem_ne
        (show 1 < (G.neighborFinset a).card by change 1 < G.degree a; omega) v
      have hau : G.Adj a u := (G.mem_neighborFinset _ _).mp hu
      have hdu : G.degree u ≠ 2 := by
        intro hdu
        exact no_low_walk (by omega) S hS b v a u hb.symm ha hau (Ne.symm hab)
          (Ne.symm huv) hdb hdv hda hdu
      have hue := unique v a u ha hau hdu
      simpa only [hue] using (show G.Adj a u ∧ u ≠ v from ⟨hau,huv⟩)
    obtain ⟨hah,hhv⟩ := other a b hva hvb hab hda hdb
    obtain ⟨hbh,_⟩ := other b a hvb hva (Ne.symm hab) hdb hda
    exact no_low_cycle (by omega) S hS v a (high v) b hva hah.symm hbh.symm hvb
      (Ne.symm hhv) hab hdv hda (high_degree v) hdb
  have hH : H = {Sum.inl A, Sum.inr C} := by
    ext v
    rcases v with i|j
    · by_cases hi : i = A
      · subst i; simp [H, L, G, (incidence_degrees S).1, hA]
      · simp [H, L, G, (incidence_degrees S).1, hrows i hi, hi]
    · by_cases hj : j = C
      · subst j; simp [H, L, G, (incidence_degrees S).2, hC]
      · simp [H, L, G, (incidence_degrees S).2, hcols j hj, hj]
  have hL : L.card = 8 := by
    have ht : H.card + L.card = 10 := by
      simpa only [H, card_univ, Fintype.card_sum, Fintype.card_fin] using
        card_sdiff_add_card_eq_card (show L ⊆ univ from subset_univ _)
    rw [hH] at ht
    rw [card_pair (by simp)] at ht
    omega
  have hsumH : (∑ v ∈ H, G.degree v) = 6 := by
    rw [hH, sum_pair (by simp)]
    simp only [G, (incidence_degrees S).1, (incidence_degrees S).2, hA, hC]
  have hsumLow : L.card ≤ ∑ v ∈ L, (neighborsIn G H v).card := by
    calc
      _ = ∑ _v ∈ L, 1 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        have hs := card_filter_add_card_filter_not (s := G.neighborFinset v) (fun w => w ∈ L)
        have h1 : (G.neighborFinset v).filter (fun w => w ∈ L) = neighborsIn G L v := by
          ext w; simp [neighborsIn, and_comm]
        have h2 : (G.neighborFinset v).filter (fun w => w ∉ L) = neighborsIn G H v := by
          ext w; simp [neighborsIn, H, and_comm]
        rw [h1,h2] at hs
        change (neighborsIn G L v).card + (neighborsIn G H v).card = G.degree v at hs
        have := local_bound v hv
        have := (mem_filter.mp hv).2
        omega
  have hb := boundary_le_degree G L
  change (∑ v ∈ L, (neighborsIn G H v).card) ≤ ∑ v ∈ H, G.degree v at hb
  omega

end D5.S3.Combinatorics.Graph.DirectSquareWeakFour
