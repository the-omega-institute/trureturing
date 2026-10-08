/- GID: D5/S3/Combinatorics/SignedDoubleRoman/CubicBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/CubicBound
   mirror-E: none(waiver:cubic-signed-double-roman-bound)
   anchors: []
   utility: none
   digest: Cubic graphs have signed double Roman two-domination number at most their order. -/

import D5.S3.Combinatorics.SignedDoubleRoman.MixedPacking
import D5.S3.Combinatorics.SignedDoubleRoman.PackingLabel

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.CubicBound

open Finset MixedDefs

/-- Problem 3.1 of Amjadi, Yang, Nazari-Moghaddam, Sheikholeslami and Shao. -/
theorem result : CubicDefs.claim := by
  intro V _ _ G _ hdeg
  classical
  have hs : Supported (⊥ : SimpleGraph V) G univ := by
    intro u v _
    exact ⟨mem_univ _, mem_univ _⟩
  have hd : DegreeBound (⊥ : SimpleGraph V) G univ := by
    intro v _
    change ((⊥ : SimpleGraph V).neighborFinset v).card + (G.neighborFinset v).card ≤ 3
    simp only [SimpleGraph.neighborFinset_bot, card_empty, Nat.zero_add, hdeg, le_refl]
  have hn : (⊥ : SimpleGraph V).CliqueFreeOn ((univ : Finset V) : Set V) 4 := by
    intro K _ hK
    obtain ⟨hc, hk⟩ := (⊥ : SimpleGraph V).isNClique_iff.mp hK
    obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (by omega : 1 < K.card)
    simpa using hc hu hv huv
  obtain ⟨B, _, hB, hsize⟩ := MixedPacking.large_mixed_packing (⊥ : SimpleGraph V) G
    univ hs hd hn
  apply PackingLabel.gamma_le_of_packing G hdeg B hB.2
  simpa only [card_univ] using hsize

#print axioms result

end D5.S3.Combinatorics.SignedDoubleRoman.CubicBound
