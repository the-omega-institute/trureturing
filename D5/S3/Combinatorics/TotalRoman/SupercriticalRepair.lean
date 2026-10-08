/- GID: D5/S3/Combinatorics/TotalRoman/SupercriticalRepair
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/SupercriticalRepair
   mirror-E: none(waiver:local-edge-repair)
   anchors: []
   utility: none
   digest: Two-vertex repairs produce optimal functions supporting both non-edge endpoints. -/

import D5.S3.Combinatorics.TotalRoman.SupercriticalBasics

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.SupercriticalRepair

open SupercriticalDefs SupercriticalBasics

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem raise_two (f : V → ℕ) (a b : V) (hbound : ∀ z, f z ≤ 2)
    (hzero : ∀ z, f z = 0 → z ≠ a → z ≠ b → ∃ w, G.Adj z w ∧ f w = 2)
    (hpos : ∀ z, 0 < f z → ∃ w, G.Adj z w ∧ (0 < f w ∨ w = a ∨ w = b))
    (ha : ∃ w, G.Adj a w ∧ (0 < f w ∨ w = a ∨ w = b))
    (hb : ∃ w, G.Adj b w ∧ (0 < f w ∨ w = a ∨ w = b)) :
    ∃ g : V → ℕ, IsTRDF G g ∧ (∑ z, g z) ≤ (∑ z, f z) + 2 ∧
      (∀ z, f z ≤ g z) ∧ 0 < g a ∧ 0 < g b := by
  classical
  let g : V → ℕ := fun z => if z = a ∨ z = b then max (f z) 1 else f z
  have hmono : ∀ z, f z ≤ g z := by
    intro z
    dsimp [g]
    split_ifs <;> omega
  have hga : 0 < g a := by simp [g]
  have hgb : 0 < g b := by simp [g]
  have hgood : ∀ z w, G.Adj z w → (0 < f w ∨ w = a ∨ w = b) →
      ∃ t, G.Adj z t ∧ 0 < g t := by
    intro z w hzw hw
    refine ⟨w, hzw, ?_⟩
    rcases hw with hw | rfl | rfl
    · have := hmono w
      omega
    · exact hga
    · exact hgb
  have hg : IsTRDF G g := by
    refine ⟨?_, ?_, ?_⟩
    · intro z
      have := hbound z
      dsimp [g]
      split_ifs <;> omega
    · intro z hz
      have hfz : f z = 0 := by have := hmono z; omega
      have hza : z ≠ a := by intro he; subst z; omega
      have hzb : z ≠ b := by intro he; subst z; omega
      obtain ⟨w, hzw, hw⟩ := hzero z hfz hza hzb
      refine ⟨w, hzw, ?_⟩
      dsimp [g]
      split_ifs <;> omega
    · intro z hz
      by_cases hza : z = a
      · subst z
        obtain ⟨w, hw, hfw⟩ := ha
        exact hgood a w hw hfw
      by_cases hzb : z = b
      · subst z
        obtain ⟨w, hw, hfw⟩ := hb
        exact hgood b w hw hfw
      have hfz : 0 < f z := by simpa [g, hza, hzb] using hz
      obtain ⟨w, hw, hfw⟩ := hpos z hfz
      exact hgood z w hw hfw
  have hs : (∑ z, g z) ≤ ∑ z, (f z + (if z = a then 1 else 0) +
      (if z = b then 1 else 0)) := by
    apply Finset.sum_le_sum
    intro z _
    dsimp [g]
    split_ifs <;> simp_all
    omega
  have hw : (∑ z, g z) ≤ (∑ z, f z) + 2 := by
    simpa [Finset.sum_add_distrib, Finset.sum_ite_eq'] using hs
  exact ⟨g, hg, hw, hmono, hga, hgb⟩

theorem repair (hG : ∀ z, ∃ w, G.Adj z w) (u v : V)
    (hgap : gammaTR (G ⊔ SimpleGraph.edge u v) + 2 ≤ gammaTR G) :
    ∃ g : V → ℕ, IsTRDF G g ∧ ∑ z, g z = gammaTR G ∧ 0 < g u ∧ 0 < g v := by
  classical
  obtain ⟨f, hf, hw⟩ := attained (G := G ⊔ SimpleGraph.edge u v) (by
    intro z
    obtain ⟨w, hzw⟩ := hG z
    exact ⟨w, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hzw)⟩)
  have hadj : ∀ z w, (G ⊔ SimpleGraph.edge u v).Adj z w →
      G.Adj z w ∨ (z = u ∧ w = v) ∨ (z = v ∧ w = u) := by
    intro z w h
    rcases (SimpleGraph.sup_adj _ _ _ _).1 h with h | h
    · exact Or.inl h
    · exact Or.inr ((SimpleGraph.edge_adj u v z w).1 h).1
  have finish : ∀ g : V → ℕ, IsTRDF G g → (∑ z, g z) ≤ (∑ z, f z) + 2 →
      0 < g u → 0 < g v →
      ∃ g : V → ℕ, IsTRDF G g ∧ ∑ z, g z = gammaTR G ∧ 0 < g u ∧ 0 < g v := by
    intro g hg hsum hgu hgv
    have hlo := le_weight hg
    refine ⟨g, hg, ?_, hgu, hgv⟩
    omega
  have small_impossible : ¬ (f u ≤ 1 ∧ f v ≤ 1 ∧ (f u = 0 ∨ f v = 0)) := by
    rintro ⟨hu, hv, hz⟩
    have hfg : IsTRDF G f := by
      refine ⟨hf.1, ?_, ?_⟩
      · intro z hfz
        obtain ⟨w, hzw, hfw⟩ := hf.2.1 z hfz
        refine ⟨w, ?_, hfw⟩
        rcases hadj z w hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · omega
        · omega
      · intro z hfz
        obtain ⟨w, hzw, hfw⟩ := hf.2.2 z hfz
        refine ⟨w, ?_, hfw⟩
        rcases hadj z w hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h
        · rcases hz with hz | hz <;> omega
        · rcases hz with hz | hz <;> omega
    have := le_weight hfg
    omega
  have zero_repair : ∀ p q : V, (p = u ∧ q = v) ∨ (p = v ∧ q = u) →
      f p = 0 → f q = 2 →
      ∃ g : V → ℕ, IsTRDF G g ∧ ∑ z, g z = gammaTR G ∧ 0 < g u ∧ 0 < g v := by
    intro p q hpq hp hq
    obtain ⟨a, ha⟩ := hG p
    have hzer : ∀ z, f z = 0 → z ≠ p → z ≠ a → ∃ w, G.Adj z w ∧ f w = 2 := by
      intro z hz hzp _
      obtain ⟨w, hzw, hw⟩ := hf.2.1 z hz
      refine ⟨w, ?_, hw⟩
      rcases hadj z w hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
      · rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    have hpos : ∀ z, 0 < f z → ∃ w, G.Adj z w ∧ (0 < f w ∨ w = p ∨ w = a) := by
      intro z hz
      obtain ⟨w, hzw, hw⟩ := hf.2.2 z hz
      refine ⟨w, ?_, Or.inl hw⟩
      rcases hadj z w hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h
      · rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
      · rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    obtain ⟨g, hg, hs, hm, hgp, _⟩ := raise_two f p a hf.1 hzer hpos
      ⟨a, ha, Or.inr (Or.inr rfl)⟩ ⟨p, ha.symm, Or.inr (Or.inl rfl)⟩
    have hgq : 0 < g q := by have := hm q; omega
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact finish g hg hs hgp hgq
    · exact finish g hg hs hgq hgp
  by_cases hu : f u = 0
  · have hv : f v = 2 := by
      have := hf.1 v
      by_contra h
      apply small_impossible
      exact ⟨by omega, by omega, Or.inl hu⟩
    exact zero_repair u v (Or.inl ⟨rfl, rfl⟩) hu hv
  by_cases hv : f v = 0
  · have hu' : f u = 2 := by
      have := hf.1 u
      by_contra h
      apply small_impossible
      exact ⟨by omega, by omega, Or.inr hv⟩
    exact zero_repair v u (Or.inr ⟨rfl, rfl⟩) hv hu'
  have hfu : 0 < f u := by omega
  have hfv : 0 < f v := by omega
  obtain ⟨a, ha⟩ := hG u
  obtain ⟨b, hb⟩ := hG v
  have hzer : ∀ z, f z = 0 → z ≠ a → z ≠ b → ∃ w, G.Adj z w ∧ f w = 2 := by
    intro z hz _ _
    obtain ⟨w, hzw, hw⟩ := hf.2.1 z hz
    refine ⟨w, ?_, hw⟩
    rcases hadj z w hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · omega
    · omega
  have hpos : ∀ z, 0 < f z → ∃ w, G.Adj z w ∧ (0 < f w ∨ w = a ∨ w = b) := by
    intro z hz
    obtain ⟨w, hzw, hw⟩ := hf.2.2 z hz
    rcases hadj z w hzw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨w, h, Or.inl hw⟩
    · exact ⟨a, ha, Or.inr (Or.inl rfl)⟩
    · exact ⟨b, hb, Or.inr (Or.inr rfl)⟩
  obtain ⟨g, hg, hs, hm, _, _⟩ := raise_two f a b hf.1 hzer hpos
    ⟨u, ha.symm, Or.inl hfu⟩ ⟨v, hb.symm, Or.inl hfv⟩
  apply finish g hg hs
  · have := hm u
    omega
  · have := hm v
    omega

end D5.S3.Combinatorics.TotalRoman.SupercriticalRepair
