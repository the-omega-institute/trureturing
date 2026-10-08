/- GID: D5/S3/Combinatorics/TotalRoman/SupercriticalCliqueUnion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/SupercriticalCliqueUnion
   mirror-E: none(waiver:external-conjecture-resolution)
   anchors: []
   utility: none
   digest: Adjoining a clique of order at least three makes a supercritical graph edge-critical. -/

import D5.S3.Combinatorics.TotalRoman.SupercriticalSupport
import D5.S3.Combinatorics.TotalRoman.SupercriticalUnion

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.SupercriticalCliqueUnion

open SupercriticalDefs SupercriticalBasics SupercriticalUnion

theorem result : SupercriticalDefs.claimCliqueUnion := by
  classical
  intro V _ _ G k n hG hk hn
  let K : SimpleGraph (Fin n) := ⊤
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  have hK : ∀ w, ∃ z, K.Adj w z := by
    intro w
    by_cases hw : w = a
    · subst w
      exact ⟨b, (SimpleGraph.top_adj _ _).2 hab⟩
    · exact ⟨a, (SimpleGraph.top_adj _ _).2 hw⟩
  have hgammaK : gammaTR K = 3 := by
    have hup := universal_bound (G := K) a b ((SimpleGraph.top_adj _ _).2 hab)
      (fun x hx => (SimpleGraph.top_adj _ _).2 hx.symm)
    obtain ⟨f, hf, hw⟩ := attained hK
    have hlo := weight_three hf (by simpa using hn)
    omega
  have hbase : gammaTR (G ⊕g K) = k + 3 := by
    rw [additivity hG.1.1 hK, hk, hgammaK]
  have mono : ∀ {X : Type} (A B : SimpleGraph X) (f : X → ℕ),
      (∀ x y, A.Adj x y → B.Adj x y) → IsTRDF A f → IsTRDF B f := by
    intro X A B f hm hf
    refine ⟨hf.1, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, hfy⟩ := hf.2.1 x hx
      exact ⟨y, hm x y hy, hfy⟩
    · intro x hx
      obtain ⟨y, hy, hfy⟩ := hf.2.2 x hx
      exact ⟨y, hm x y hy, hfy⟩
  have inside : ∀ u v : V, u ≠ v → ¬ G.Adj u v →
      gammaTR ((G ⊕g K) ⊔ SimpleGraph.edge (.inl u) (.inl v)) < gammaTR (G ⊕g K) := by
    intro u v huv hnu
    obtain ⟨f, hf, hwf⟩ := attained (G := G ⊔ SimpleGraph.edge u v) (by
      intro x
      obtain ⟨y, hxy⟩ := hG.1.1 x
      exact ⟨y, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hxy)⟩)
    obtain ⟨g, hg, hwg⟩ := attained hK
    have hfg : IsTRDF ((G ⊔ SimpleGraph.edge u v) ⊕g K) (Sum.elim f g) :=
      (sum_trdf _).2 ⟨hf, hg⟩
    have hfg' : IsTRDF ((G ⊕g K) ⊔ SimpleGraph.edge (.inl u) (.inl v))
        (Sum.elim f g) := by
      apply mono _ _ _ _ hfg
      rintro (x | x) (y | y) hxy
      · rcases (SimpleGraph.sup_adj _ _ _ _).1 hxy with hxy | hxy
        · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hxy)
        · apply (SimpleGraph.sup_adj _ _ _ _).2
          right
          simpa [SimpleGraph.edge_adj] using hxy
      · simp at hxy
      · simp at hxy
      · exact (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hxy)
    have hup := le_weight hfg'
    rw [Fintype.sum_sum_type] at hup
    change gammaTR ((G ⊕g K) ⊔ SimpleGraph.edge (.inl u) (.inl v)) ≤
      (∑ x, f x) + ∑ x, g x at hup
    rw [hwf, hwg, hgammaK] at hup
    have hgap := hG.2 u v huv hnu
    omega
  have cross : ∀ u : V, ∀ v : Fin n,
      gammaTR ((G ⊕g K) ⊔ SimpleGraph.edge (.inl u) (.inr v)) < gammaTR (G ⊕g K) := by
    intro u v
    obtain ⟨f, hf, hw, hfu⟩ := SupercriticalSupport.result V G hG u
    let q : V ⊕ Fin n → ℕ := Sum.elim f (fun w => if w = v then 2 else 0)
    have hq : IsTRDF ((G ⊕g K) ⊔ SimpleGraph.edge (.inl u) (.inr v)) q := by
      refine ⟨?_, ?_, ?_⟩
      · rintro (x | w)
        · exact hf.1 x
        · dsimp [q]
          split_ifs <;> omega
      · rintro (x | w) hx
        · obtain ⟨y, hy, hfy⟩ := hf.2.1 x hx
          exact ⟨.inl y, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hy), hfy⟩
        · have hwv : w ≠ v := by intro he; subst w; simp [q] at hx
          refine ⟨.inr v, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl ?_), ?_⟩
          · exact (SimpleGraph.top_adj _ _).2 hwv
          · simp [q]
      · rintro (x | w) hx
        · obtain ⟨y, hy, hfy⟩ := hf.2.2 x hx
          exact ⟨.inl y, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hy), hfy⟩
        · have hwv : w = v := by
            by_contra hwv
            simp [q, hwv] at hx
          subst w
          refine ⟨.inl u, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inr ?_), hfu⟩
          simp [SimpleGraph.edge_adj]
    have hup := le_weight hq
    have hweight : (∑ x, q x) = k + 2 := by
      rw [Fintype.sum_sum_type]
      change (∑ x, f x) + (∑ w : Fin n, if w = v then 2 else 0) = k + 2
      simp [hw, hk]
    rw [hweight] at hup
    omega
  refine ⟨?_, hbase, ?_⟩
  · constructor
    · rintro (v | w)
      · obtain ⟨u, hu⟩ := hG.1.1 v
        exact ⟨.inl u, (SimpleGraph.sum_adj_inl).2 hu⟩
      · obtain ⟨z, hz⟩ := hK w
        exact ⟨.inr z, (SimpleGraph.sum_adj_inr).2 hz⟩
    · obtain ⟨u, v, huv, hnu⟩ := hG.1.2
      exact ⟨.inl u, .inl v, by simpa using huv, by simpa using hnu⟩
  · rintro (u | u) (v | v) huv hnu
    · exact inside u v (by simpa using huv) (by simpa using hnu)
    · exact cross u v
    · rw [SimpleGraph.edge_comm]
      exact cross v u
    · exact False.elim (hnu ((SimpleGraph.sum_adj_inr).2
        ((SimpleGraph.top_adj _ _).2 (by simpa using huv))))

#print axioms result

end D5.S3.Combinatorics.TotalRoman.SupercriticalCliqueUnion
