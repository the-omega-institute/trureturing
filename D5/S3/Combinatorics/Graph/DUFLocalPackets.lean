/- GID: D5/S3/Combinatorics/Graph/DUFLocalPackets
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFLocalPackets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: Mixed actual local vertices correspond exactly to unique common-link packet rows. -/

import D5.S3.Combinatorics.Graph.DUFReciprocal
import D5.S3.Combinatorics.Graph.DUFPacketOwnership

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFLocalPackets

open Finset DUFStructure DUFReciprocal DUFPacketOwnership

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A mixed vertex of the actual local graph determines a unique triangle packet
whose row contains the original triple, and every such packet makes the vertex mixed. -/
theorem mixed_packet_correspondence (H : Finset (Finset V)) (hd : DUF H)
    (e : Finset V) (he : e ∈ H) (he3 : e.card = 3)
    (w : V × V) (hw : w ∈ localVertices H e) :
    (∃ r ∈ localNeighbors H e w, ∃ z ∈ localNeighbors H e w, r.1 ≠ z.1) ↔
      ∃! T : Finset V, PacketRow H {w.1, w.2} T w.1 e := by
  classical
  rcases w with ⟨u, v⟩
  obtain ⟨hu, hv, hvH⟩ := (mem_filter.mp hw).2
  have huv : u ≠ v := fun h => hv (h ▸ hu)
  constructor
  · intro hm
    have hc := local_correspondence H hd e he he3 (u, v) hw
    have hk3 : (common H {u, v}).card = 3 := by
      have := hc.2 hm
      dsimp only at hc
      omega
    obtain ⟨⟨a, c⟩, hr, ⟨b, d⟩, hz, hab⟩ := hm
    simp only [localNeighbors, mem_filter, adjacent] at hr hz
    obtain ⟨hrV, hua, hvc, hrcH⟩ := hr
    obtain ⟨hzV, hub, hvd, hzdH⟩ := hz
    obtain ⟨ha, hcE, hcH⟩ := (mem_filter.mp hrV).2
    obtain ⟨hb, hdE, hdH⟩ := (mem_filter.mp hzV).2
    change a ≠ b at hab
    have heq : e = {u, a, b} := by
      have hs : ({u, a, b} : Finset V) ⊆ e := by
        simp only [insert_subset_iff, singleton_subset_iff]
        exact ⟨hu, ha, hb⟩
      exact (eq_of_subset_of_card_le hs (by simp [he3, hua, hub, hab])).symm
    have hcu : c ≠ u := fun h => hcE (h.symm ▸ hu)
    have hca : c ≠ a := fun h => hcE (h.symm ▸ ha)
    have hcb : c ≠ b := fun h => hcE (h.symm ▸ hb)
    have hdu : d ≠ u := fun h => hdE (h.symm ▸ hu)
    have hda : d ≠ a := fun h => hdE (h.symm ▸ ha)
    have hdb : d ≠ b := fun h => hdE (h.symm ▸ hb)
    have hva : v ≠ a := fun h => hv (h.symm ▸ ha)
    have hvb : v ≠ b := fun h => hv (h.symm ▸ hb)
    have hbase : ({a, b} : Finset V) ∈ common H {u, v} := by
      simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
        insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
      refine ⟨by simp [hab], ⟨by simp [hua, hub], ?_⟩,
        ⟨by simp [hva, hvb], ?_⟩⟩
      · simpa [heq] using he
      · simpa [heq, hua, hub] using hvH
    have hbc : ({b, c} : Finset V) ∈ common H {u, v} := by
      simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
        insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
      refine ⟨by simp [hcb.symm], ⟨by simp [hub, hcu.symm], ?_⟩,
        ⟨by simp [hvb, hvc], ?_⟩⟩
      · convert hcH using 1
        ext t
        simp [heq, hua, hab, erase_insert_of_ne, or_comm, or_left_comm]
      · simpa [heq, hua, hub, hab, hab.symm, erase_insert_of_ne, insert_comm, pair_comm]
          using hrcH
    have had : ({a, d} : Finset V) ∈ common H {u, v} := by
      simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
        insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
      refine ⟨by simp [hda.symm], ⟨by simp [hua, hdu.symm], ?_⟩,
        ⟨by simp [hva, hvd], ?_⟩⟩
      · convert hdH using 1
        ext t
        simp [heq, hub, hab, erase_insert_of_ne, or_comm, or_left_comm]
      · simpa [heq, hua, hub, hab, hab.symm, erase_insert_of_ne, insert_comm, pair_comm]
          using hzdH
    have hcd : c = d := by
      have hi := common_intersecting H hd {u, v} (by simp [huv]) {b, c} hbc {a, d} had
      by_contra hne
      exact hi (by simp [disjoint_left, hab.symm, hdb.symm, hca, hne])
    subst d
    have hT3 : ({a, b, c} : Finset V).card = 3 := by simp [hab, hca.symm, hcb.symm]
    have hsub : ({a, b, c} : Finset V).powersetCard 2 ⊆ common H {u, v} := by
      intro p hp
      obtain ⟨hpT, hp2⟩ := mem_powersetCard.mp hp
      obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hp2
      simp only [insert_subset_iff, singleton_subset_iff, mem_insert, mem_singleton] at hpT
      rcases hpT with ⟨hx, hy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact (hxy rfl).elim
      · exact hbase
      · exact had
      · simpa only [pair_comm] using hbase
      · exact (hxy rfl).elim
      · exact hbc
      · simpa only [pair_comm] using had
      · simpa only [pair_comm] using hbc
      · exact (hxy rfl).elim
    have hK : common H {u, v} = ({a, b, c} : Finset V).powersetCard 2 := by
      apply (eq_of_subset_of_card_le hsub ?_).symm
      rw [hk3, card_powersetCard, hT3]
      decide
    refine ⟨{a, b, c}, ?_, ?_⟩
    · exact ⟨by simp [huv], hT3, hK, by simp,
        {a, b}, by simp [mem_powersetCard, hab], heq⟩
    · intro T hT
      exact eq_of_powersetCard_eq (hT.2.1.trans hT3.symm) (by decide)
        (by rw [hT.2.1]; decide) (hT.2.2.1.symm.trans hK)
  · rintro ⟨T, hT, _⟩
    obtain ⟨_, hT3, hK, _, p, hp, hep⟩ := hT
    obtain ⟨hpT, hp2⟩ := mem_powersetCard.mp hp
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hp2
    obtain ⟨c, hc⟩ := card_eq_one.mp (show (T \ {a, b}).card = 1 by
      rw [card_sdiff_of_subset hpT, hT3]
      simp [hab])
    have hcT : c ∈ T := (mem_sdiff.mp (hc.symm ▸ mem_singleton_self c)).1
    have hcp : c ∉ ({a, b} : Finset V) :=
      (mem_sdiff.mp (hc.symm ▸ mem_singleton_self c)).2
    have hca : c ≠ a := fun h => hcp (by simp [h])
    have hcb : c ≠ b := fun h => hcp (by simp [h])
    have hTeq : T = insert c {a, b} := by
      rw [← singleton_union, ← hc, sdiff_union_of_subset hpT]
    have extend (r : Finset V) (hr : r ∈ T.powersetCard 2) (i : V)
        (hi : i ∈ ({u, v} : Finset V)) : i ∉ r ∧ insert i r ∈ H := by
      have hm : r ∈ common H {u, v} := hK.symm ▸ hr
      have := (mem_filter.mp hm).2 hi
      simpa only [neighbors, mem_filter, mem_univ, true_and] using this
    have habT : ({a, b} : Finset V) ∈ T.powersetCard 2 :=
      mem_powersetCard.mpr ⟨hpT, by simp [hab]⟩
    have hacT : ({a, c} : Finset V) ∈ T.powersetCard 2 := by
      simp [mem_powersetCard, hTeq, insert_subset_iff, hca.symm]
    have hbcT : ({b, c} : Finset V) ∈ T.powersetCard 2 := by
      simp [mem_powersetCard, hTeq, insert_subset_iff, hcb.symm]
    have huab := extend {a, b} habT u (by simp)
    have huac := extend {a, c} hacT u (by simp)
    have hubc := extend {b, c} hbcT u (by simp)
    have hvac := extend {a, c} hacT v (by simp)
    have hvbc := extend {b, c} hbcT v (by simp)
    have hua : u ≠ a := fun h => huab.1 (by simp [h])
    have hub : u ≠ b := fun h => huab.1 (by simp [h])
    have huc : u ≠ c := fun h => huac.1 (by simp [h])
    have hvc : v ≠ c := fun h => hvac.1 (by simp [h])
    have hcE : c ∉ e := by simp [hep, huc.symm, hca, hcb]
    refine ⟨(a, c), ?_, (b, c), ?_, hab⟩
    · simp only [localNeighbors, localVertices, adjacent, mem_filter, mem_univ, true_and]
      refine ⟨⟨by simp [hep], hcE, ?_⟩, hua, hvc, ?_⟩
      · convert hubc.2 using 1
        ext t
        simp [hep, hua, hab, erase_insert_of_ne, or_comm, or_left_comm]
      · simpa [hep, hua, hub, hab, hab.symm, erase_insert_of_ne, insert_comm, pair_comm]
          using hvbc.2
    · simp only [localNeighbors, localVertices, adjacent, mem_filter, mem_univ, true_and]
      refine ⟨⟨by simp [hep], hcE, ?_⟩, hub, hvc, ?_⟩
      · convert huac.2 using 1
        ext t
        simp [hep, hub, hab, erase_insert_of_ne, or_comm, or_left_comm]
      · simpa [hep, hua, hub, hab, hab.symm, erase_insert_of_ne, insert_comm, pair_comm]
          using hvac.2

end D5.S3.Combinatorics.Graph.DUFLocalPackets
