/- GID: D5/S3/Combinatorics/TotalRoman/DiameterTwoRepair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/DiameterTwoRepair
   mirror-E: none(waiver:singleton-edge-repair)
   anchors: []
   utility: none
   digest: Oriented singleton certificates lift edge repairs through clique expansions. -/

import D5.S3.Combinatorics.TotalRoman.DiameterTwoConstruction
import D5.S3.Combinatorics.TotalRoman.DiameterTwoWeight

set_option autoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Combinatorics.TotalRoman.DiameterTwoRepair

open SupercriticalDefs SupercriticalBasics DiameterTwoConstruction DiameterTwoWeight

/-- A repaired non-edge has total Roman number exactly four at every order. -/
theorem repaired {n : ℕ} (hn : 10 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (hgap : ¬ (family n).Adj a b) :
    gammaTR (family n ⊔ SimpleGraph.edge a b) = 4 := by
  classical
  have hc : ∀ i j : Fin 10, i ≠ j → ¬ seed.Adj i j → ∃ z : Fin 10,
      (j ≠ 1 ∧ ∀ k, k ≠ j → seed.Adj k i ∨ seed.Adj k z) ∨
      (i ≠ 1 ∧ ∀ k, k ≠ i → seed.Adj k j ∨ seed.Adj k z) := by
    decide
  have hdiff : project a ≠ project b := by
    intro he
    exact hgap ⟨hab, Or.inl he⟩
  have hnon : ¬ seed.Adj (project a) (project b) := by
    intro he
    exact hgap (lift_adj he)
  have upper_oriented (x y : Fin n) (hxy : x ≠ y) (z : Fin 10)
      (hy : project y ≠ 1)
      (hcover : ∀ k, k ≠ project y → seed.Adj k (project x) ∨ seed.Adj k z) :
      gammaTR (family n ⊔ SimpleGraph.edge x y) ≤ 4 := by
    have hd : ∀ w : Fin n, ∃ u ∈ ({x, Fin.castLE hn z} : Finset (Fin n)),
        (family n ⊔ SimpleGraph.edge x y).Adj w u := by
      intro w
      by_cases he : project w = project y
      · have hwy : w = y :=
          (singleton hn w (project y) hy he).trans
            (singleton hn y (project y) hy rfl).symm
        subst w
        refine ⟨x, by simp, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ?_)⟩
        exact (SimpleGraph.edge_adj x y y x).2 ⟨Or.inr ⟨rfl, rfl⟩, hxy.symm⟩
      · rcases hcover (project w) he with h | h
        · exact ⟨x, by simp, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl (lift_adj h))⟩
        · refine ⟨Fin.castLE hn z, by simp, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl ?_)⟩
          exact lift_adj (by simpa [project_rep] using h)
    have hb := doubled_bound (family n ⊔ SimpleGraph.edge x y) _ hd
    have hsize : ({x, Fin.castLE hn z} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    omega
  have hu : gammaTR (family n ⊔ SimpleGraph.edge a b) ≤ 4 := by
    obtain ⟨z, hz | hz⟩ := hc (project a) (project b) hdiff hnon
    · exact upper_oriented a b hab z hz.1 hz.2
    · simpa [SimpleGraph.edge_comm] using upper_oriented b a hab.symm z hz.1 hz.2
  have hiso : ∀ w : Fin n, ∃ u, (family n).Adj w u := by
    intro w
    obtain ⟨u, _, hu⟩ := total_domination hn w
    exact ⟨u, hu⟩
  obtain ⟨f, hf, hw⟩ := attained (G := family n ⊔ SimpleGraph.edge a b) (by
    intro w
    obtain ⟨u, hu⟩ := hiso w
    exact ⟨u, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hu)⟩)
  have hl : 4 ≤ gammaTR (family n ⊔ SimpleGraph.edge a b) := by
    by_contra hh
    obtain ⟨v, hv⟩ := universal_of_weight_le_three
      (by simpa using (show 4 ≤ n by omega)) hf (by omega)
    obtain ⟨w, hwv, hwa, hnotv, hnota⟩ := obstruction hn v a
    rcases (SimpleGraph.sup_adj _ _ _ _).1 (hv w hwv) with h | h
    · exact hnotv h
    · rcases ((SimpleGraph.edge_adj a b w v).1 h).1 with h | h
      · exact hwa h.1
      · have hv_eq : v = a := h.2
        obtain ⟨u, hua, hub, hnota, hnotb⟩ := obstruction hn a b
        rcases (SimpleGraph.sup_adj _ _ _ _).1 (hv u (by simpa [hv_eq] using hua))
          with h | h
        · exact hnota (by simpa [hv_eq] using h)
        · rcases ((SimpleGraph.edge_adj a b u v).1 h).1 with h | h
          · exact hua h.1
          · exact hub h.1
  omega

end D5.S3.Combinatorics.TotalRoman.DiameterTwoRepair
