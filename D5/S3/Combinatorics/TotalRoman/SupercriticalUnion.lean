/- GID: D5/S3/Combinatorics/TotalRoman/SupercriticalUnion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/SupercriticalUnion
   mirror-E: none(waiver:disjoint-union-additivity)
   anchors: []
   utility: none
   digest: Total Roman domination is additive over disjoint unions without isolated vertices. -/

import D5.S3.Combinatorics.TotalRoman.SupercriticalBasics

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.SupercriticalUnion

open SupercriticalDefs SupercriticalBasics

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem sum_trdf (f : V ⊕ W → ℕ) :
    IsTRDF (G ⊕g H) f ↔ IsTRDF G (fun v => f (.inl v)) ∧
      IsTRDF H (fun w => f (.inr w)) := by
  constructor
  · intro hf
    constructor
    · refine ⟨fun v => hf.1 (.inl v), ?_, ?_⟩
      · intro v hv
        obtain ⟨u, hu, hfu⟩ := hf.2.1 (.inl v) hv
        cases u with
        | inl u => exact ⟨u, (SimpleGraph.sum_adj_inl).1 hu, hfu⟩
        | inr u => simp at hu
      · intro v hv
        obtain ⟨u, hu, hfu⟩ := hf.2.2 (.inl v) hv
        cases u with
        | inl u => exact ⟨u, (SimpleGraph.sum_adj_inl).1 hu, hfu⟩
        | inr u => simp at hu
    · refine ⟨fun w => hf.1 (.inr w), ?_, ?_⟩
      · intro w hw
        obtain ⟨u, hu, hfu⟩ := hf.2.1 (.inr w) hw
        cases u with
        | inl u => simp at hu
        | inr u => exact ⟨u, (SimpleGraph.sum_adj_inr).1 hu, hfu⟩
      · intro w hw
        obtain ⟨u, hu, hfu⟩ := hf.2.2 (.inr w) hw
        cases u with
        | inl u => simp at hu
        | inr u => exact ⟨u, (SimpleGraph.sum_adj_inr).1 hu, hfu⟩
  · rintro ⟨hg, hh⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro (v | w)
      · exact hg.1 v
      · exact hh.1 w
    · rintro (v | w) hz
      · obtain ⟨u, hu, hfu⟩ := hg.2.1 v hz
        exact ⟨.inl u, (SimpleGraph.sum_adj_inl).2 hu, hfu⟩
      · obtain ⟨u, hu, hfu⟩ := hh.2.1 w hz
        exact ⟨.inr u, (SimpleGraph.sum_adj_inr).2 hu, hfu⟩
    · rintro (v | w) hz
      · obtain ⟨u, hu, hfu⟩ := hg.2.2 v hz
        exact ⟨.inl u, (SimpleGraph.sum_adj_inl).2 hu, hfu⟩
      · obtain ⟨u, hu, hfu⟩ := hh.2.2 w hz
        exact ⟨.inr u, (SimpleGraph.sum_adj_inr).2 hu, hfu⟩

theorem additivity [Fintype V] [Fintype W]
    (hG : ∀ v, ∃ u, G.Adj v u) (hH : ∀ w, ∃ u, H.Adj w u) :
    gammaTR (G ⊕g H) = gammaTR G + gammaTR H := by
  obtain ⟨f, hf, hwf⟩ := attained hG
  obtain ⟨g, hg, hwg⟩ := attained hH
  have hfg : IsTRDF (G ⊕g H) (Sum.elim f g) := (sum_trdf _).2 ⟨hf, hg⟩
  have hup := le_weight hfg
  rw [Fintype.sum_sum_type] at hup
  change gammaTR (G ⊕g H) ≤ (∑ v, f v) + ∑ w, g w at hup
  rw [hwf, hwg] at hup
  obtain ⟨q, hq, hwq⟩ := attained (G := G ⊕g H) (by
    rintro (v | w)
    · obtain ⟨u, hu⟩ := hG v
      exact ⟨.inl u, (SimpleGraph.sum_adj_inl).2 hu⟩
    · obtain ⟨u, hu⟩ := hH w
      exact ⟨.inr u, (SimpleGraph.sum_adj_inr).2 hu⟩)
  obtain ⟨hql, hqr⟩ := (sum_trdf q).1 hq
  have hloG := le_weight hql
  have hloH := le_weight hqr
  rw [Fintype.sum_sum_type] at hwq
  omega

end D5.S3.Combinatorics.TotalRoman.SupercriticalUnion
