/- GID: D5/S3/Combinatorics/SpectralGraph/CographVicinalWidth
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/CographVicinalWidth
   mirror-E: none
   anchors: []
   digest: Vicinal chains under complementation and component cuts. -/

import D5.S3.Combinatorics.SpectralGraph.MandalMannaDQDilworthRefutation

namespace D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth

open SimpleGraph
open MandalMannaDQDilworthRefutation (vicinal HasChainCover dilworthNumber)

private theorem vicinal_iff {V : Type} (G : SimpleGraph V) (u v : V) :
    vicinal G u v ↔ ∀ ⦃x⦄, x ≠ u → x ≠ v → G.Adj u x → G.Adj v x := by
  constructor
  · intro h x _ hx hux
    exact (Set.mem_insert_iff.mp (h hux)).resolve_left hx
  · intro h x hux
    by_cases hx : x = v
    · exact Set.mem_insert_of_mem _ (by subst x; exact Or.inl rfl)
    · exact Set.mem_insert_of_mem _ (h hux.ne.symm hx hux)

/-- Complementation reverses vicinal comparison. -/
theorem vicinal_compl_iff {V : Type} (G : SimpleGraph V) (u v : V) :
    vicinal Gᶜ u v ↔ vicinal G v u := by
  classical
  simp only [vicinal_iff, compl_adj]
  aesop

/-- Each chain assignment still works after complementation. -/
theorem hasChainCover_compl_iff {V : Type} (G : SimpleGraph V) (k : ℕ) :
    HasChainCover Gᶜ k ↔ HasChainCover G k := by
  unfold HasChainCover
  simp only [vicinal_compl_iff, or_comm]

/-- Complementation preserves the infimum of feasible chain-cover sizes. -/
theorem dilworthNumber_compl {V : Type} (G : SimpleGraph V) :
    dilworthNumber Gᶜ = dilworthNumber G := by
  simp only [dilworthNumber, hasChainCover_compl_iff]

end D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth
