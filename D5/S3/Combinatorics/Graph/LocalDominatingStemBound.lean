/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBound
   mirror-E: none(waiver:universal-finite-graph-theorem)
   anchors: []
   utility: none
   digest: The local average at a stem is at most (4n+1)/6, with equality exactly for one leaf in a star-like graph. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverageBoundEquality
import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundOmission
import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundIsomorphism

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBound

open Finset DominatingSetAverage LocalDominatingStemBoundStructure
  LocalDominatingStemBoundResidual LocalDominatingStemBoundSplit
  LocalDominatingStemBoundOmission LocalDominatingStemBoundReplication
  LocalDominatingStemBoundIsomorphism

/-- Chen–He–Lai–Li Conjecture 6.1, including its exact equality characterization. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (l : ℕ), 2 ≤ Fintype.card V → (∀ x, 0 < G.degree x) →
      leafCount G v = l → 1 ≤ l →
      avdAt G v ≤ (4 * (Fintype.card V : ℚ) + 1) / 6 ∧
        (avdAt G v = (4 * (Fintype.card V : ℚ) + 1) / 6 ↔ l = 1 ∧ StarLike G)

theorem result : claim := by
  intro V _ _ G _ v l _hn hpos hcount hl
  have hex : ∀ x, ∃ y, G.Adj x y := fun x =>
    (G.degree_pos_iff_exists_adj x).mp (hpos x)
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  have hpos : ∀ x, 0 < G.degree x := fun x =>
    (G.degree_pos_iff_exists_adj x).mpr (hex x)
  let H := residualGraph G v
  let U := residualNeighbors G v
  have hHpos : ∀ x, 0 < H.degree x := by
    intro x
    obtain ⟨y,hxy⟩ := residualGraph_no_isolates v hpos x
    exact hxy.degree_pos_left
  have hHcard : Fintype.card {x // x ∈ remaining G v} = (remaining G v).card :=
    Fintype.card_coe _
  have hrelax := relaxed_average_le H U
    (DominatingSetAverageBound.avd_le_two_thirds H hHpos)
    (fun r => DominatingSetAverageBound.avd_le_two_thirds (replicated H U r)
      (replicated_no_isolates H U r hHpos))
  have hmean : familyAverage (partialDomSets G v) ≤ 2 * (remaining G v).card / 3 := by
    simpa only [H,U,residualPartial_average,hHcard] using hrelax.1
  have hrigid : familyAverage (partialDomSets G v) = 2 * (remaining G v).card / 3 →
      partialDomSets G v = residualDomSets G v := by
    intro heq
    have heq' : familyAverage (partialSets H U) = 2 * (Fintype.card {x // x ∈ remaining G v} : ℚ) / 3 := by
      simpa only [H,U,residualPartial_average,hHcard] using heq
    have hf := hrelax.2 heq'
    have hc := congrArg Finset.card hf
    change (partialSets (residualGraph G v) (residualNeighbors G v)).card =
      (domSets (residualGraph G v)).card at hc
    rw [residualPartial_card, ← residualDomSets_card] at hc
    exact residual_equal_of_card_equal G v hc
  have hsize : Fintype.card V = (remaining G v).card + l + 1 := by
    have hs := remaining_card (G := G) v
    rw [hcount] at hs
    exact hs.symm
  have hnum := LocalDominatingStemBoundArithmetic.stem_split_bound (Fintype.card V) l
    (remaining G v).card (familyAverage (partialDomSets G v)) hsize hl hmean
  have hsplit : avdAt G v = 1 + (l : ℚ) / 2 + familyAverage (partialDomSets G v) := by
    rw [avdAt_stem_split,hcount]
  refine ⟨by simpa only [← hsplit] using hnum.1, ?_⟩
  constructor
  · intro heq
    obtain ⟨hlone,hα⟩ := hnum.2.mp (hsplit ▸ heq)
    have hf := hrigid hα
    have hβ : familyAverage (residualDomSets G v) = 2 * (remaining G v).card / 3 :=
      hf ▸ hα
    have hglob := global_equality_from_replication v (hcount.trans hlone) hf hβ
    exact ⟨hlone, (DominatingSetAverageBoundEquality.avd_eq_two_thirds_iff_starLike G hpos).mp hglob⟩
  · rintro ⟨hlone,hstar⟩
    have hL : (leafNeighbors G v).Nonempty := card_pos.mp (by
      change 0 < leafCount G v
      omega)
    have hf := starLike_partial_full v hL hstar
    have hglob := (DominatingSetAverageBoundEquality.avd_eq_two_thirds_iff_starLike G hpos).mpr hstar
    have hβ := residual_equality_from_global v (hcount.trans hlone) hf hglob
    have hα : familyAverage (partialDomSets G v) = 2 * (remaining G v).card / 3 := by
      rw [hf]
      exact hβ
    rw [hsplit]
    exact hnum.2.mpr ⟨hlone,hα⟩

end D5.S3.Combinatorics.Graph.LocalDominatingStemBound
