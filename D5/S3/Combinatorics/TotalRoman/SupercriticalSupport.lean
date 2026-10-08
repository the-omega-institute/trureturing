/- GID: D5/S3/Combinatorics/TotalRoman/SupercriticalSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TotalRoman/SupercriticalSupport
   mirror-E: none(waiver:external-conjecture-resolution)
   anchors: []
   utility: none
   digest: Every vertex of an edge-supercritical graph lies in an optimal positive support. -/

import D5.S3.Combinatorics.TotalRoman.SupercriticalRepair

set_option autoImplicit false

namespace D5.S3.Combinatorics.TotalRoman.SupercriticalSupport

open SupercriticalDefs SupercriticalBasics SupercriticalRepair

theorem result : SupercriticalDefs.claimSupport := by
  classical
  intro V _ _ G hG v
  have hnotuniv : ¬ (∀ x, x ≠ v → G.Adj v x) := by
    intro hv
    obtain ⟨w, hvw⟩ := hG.1.1 v
    have hup := universal_bound v w hvw hv
    obtain ⟨a, b, hab, hnab⟩ := hG.1.2
    obtain ⟨g, hg, hgw⟩ := attained (G := G ⊔ SimpleGraph.edge a b) (by
      intro x
      obtain ⟨y, hxy⟩ := hG.1.1 x
      exact ⟨y, (SimpleGraph.sup_adj _ _ _ _).2 (Or.inl hxy)⟩)
    have hlo := weight_two hg v
    have hgap := hG.2 a b hab hnab
    omega
  obtain ⟨u, huv, hnu⟩ : ∃ u, u ≠ v ∧ ¬ G.Adj v u := by
    by_contra h
    apply hnotuniv
    intro x hx
    by_contra hnx
    exact h ⟨x, hx, hnx⟩
  obtain ⟨f, hf, hw, hfv, _⟩ := repair hG.1.1 v u (hG.2 v u huv.symm hnu)
  exact ⟨f, hf, hw, hfv⟩

#print axioms result

end D5.S3.Combinatorics.TotalRoman.SupercriticalSupport
