/- GID: D5/S3/Combinatorics/Graph/DUFMarkedStars
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFMarkedStars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: none
   digest: A marked packet forces exact common-link stars and a neighborhood intersection. -/

import D5.S3.Combinatorics.Graph.DUFStructure

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFMarkedStars

open Finset DUFStructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common links through the two marked sides of an actual packet are exact
stars. The transverse neighborhoods meet precisely in the packet's row pair.
Neither a codegree cap nor uniformity of the whole family is assumed. -/
theorem marked_common_stars (H : Finset (Finset V)) (hd : DUF H) (u v a b c : V)
    (hdistinct : [u, v, a, b, c].Pairwise (· ≠ ·))
    (hp : common H {u, v} = ({a, b, c} : Finset V).powersetCard 2)
    (hn : neighbors H {u, b} = {a, c})
    (hk : common H {a, c} = {{u, b}, {v, b}}) :
    common H {a, b} = star c (neighbors H {a, c} ∩ neighbors H {b, c}) ∧
      common H {b, c} = star a (neighbors H {a, c} ∩ neighbors H {a, b}) ∧
      neighbors H {a, b} ∩ neighbors H {b, c} = {u, v} := by
  have first : ∀ (u v a b c : V),
      [u, v, a, b, c].Pairwise (· ≠ ·) →
      common H {u, v} = ({a, b, c} : Finset V).powersetCard 2 →
      neighbors H {u, b} = {a, c} →
      common H {a, b} = star c (neighbors H {a, c} ∩ neighbors H {b, c}) := by
    clear hdistinct hp hn hk u v a b c
    intro u v a b c hdistinct hp hn
    have hd' : (u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
        (v ≠ a ∧ v ≠ b ∧ v ≠ c) ∧ (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
      simpa [List.pairwise_cons] using hdistinct
    obtain ⟨⟨huv, hua, hub, huc⟩, ⟨hva, hvb, hvc⟩, ⟨hab, hac⟩, hbc⟩ := hd'
    have extend (p : Finset V) (hpt : p ∈ ({a, b, c} : Finset V).powersetCard 2)
        (i : V) (hi : i ∈ ({u, v} : Finset V)) : i ∉ p ∧ insert i p ∈ H := by
      have hm : p ∈ common H {u, v} := hp.symm ▸ hpt
      simpa only [neighbors, mem_filter, mem_univ, true_and] using
        (mem_filter.mp hm).2 hi
    have arms (i : V) (hi : i ∈ ({u, v} : Finset V)) :
        ({i, c} : Finset V) ∈ common H {a, b} := by
      have hiac := extend {a, c} (by simp [mem_powersetCard, hac]) i hi
      have hibc := extend {b, c} (by simp [mem_powersetCard, hbc]) i hi
      have hia : i ≠ a := fun h => hiac.1 (by simp [h])
      have hic : i ≠ c := fun h => hiac.1 (by simp [h])
      have hib : i ≠ b := fun h => hibc.1 (by simp [h])
      simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
        insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
      exact ⟨by simp [hic], ⟨by simp [hia.symm, hac], by
        simpa [insert_comm] using hiac.2⟩, ⟨by simp [hib.symm, hbc], by
        simpa [insert_comm] using hibc.2⟩⟩
    have centered (e : Finset V) (he : e ∈ common H {a, b}) : c ∈ e := by
      by_contra hce
      have hi := common_intersecting H hd {a, b} (by simp [hab])
      have hue : u ∈ e := by
        have hh := hi e he {u, c} (arms u (by simp))
        simpa [disjoint_right, hce] using hh
      have hve : v ∈ e := by
        have hh := hi e he {v, c} (arms v (by simp))
        simpa [disjoint_right, hce] using hh
      have he2 := (mem_powersetCard.mp (mem_filter.mp he).1).2
      have heq : e = {u, v} := by
        apply (eq_of_subset_of_card_le (by
          simpa only [insert_subset_iff, singleton_subset_iff] using And.intro hue hve)
          (by simpa [huv] using he2.le)).symm
      have hb := (mem_filter.mp he).2 (show b ∈ ({a, b} : Finset V) by simp)
      have hbH : insert b {u, v} ∈ H := by
        have hb' : b ∉ e ∧ insert b e ∈ H := by
          simpa only [neighbors, mem_filter, mem_univ, true_and] using hb
        simpa only [heq] using hb'.2
      have hvn : v ∈ neighbors H {u, b} := by
        simp only [neighbors, mem_filter, mem_univ, true_and]
        exact ⟨by simp [huv.symm, hvb], by
          convert hbH using 1; ext z; simp [or_comm, or_left_comm]⟩
      rw [hn] at hvn
      simp [hva, hvc] at hvn
    ext e
    constructor
    · intro he
      have hc := centered e he
      obtain ⟨x, y, hxy, heq⟩ := card_eq_two.mp
        (mem_powersetCard.mp (mem_filter.mp he).1).2
      obtain ⟨x, hxc, rfl⟩ : ∃ x, x ≠ c ∧ e = {c, x} := by
        rw [heq] at hc
        simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact ⟨y, hxy.symm, heq⟩
        · exact ⟨x, hxy, heq.trans (pair_comm _ _)⟩
      have ha := (mem_filter.mp he).2 (show a ∈ ({a, b} : Finset V) by simp)
      have hb := (mem_filter.mp he).2 (show b ∈ ({a, b} : Finset V) by simp)
      simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
        mem_singleton, not_or] at ha hb
      apply mem_image.mpr
      refine ⟨x, mem_inter.mpr ⟨?_, ?_⟩, rfl⟩
      · simp only [neighbors, mem_filter, mem_univ, true_and]
        exact ⟨by simp [Ne.symm ha.1.2, hxc], by
          convert ha.2 using 1; ext z; simp [or_comm, or_left_comm]⟩
      · simp only [neighbors, mem_filter, mem_univ, true_and]
        exact ⟨by simp [Ne.symm hb.1.2, hxc], by
          convert hb.2 using 1; ext z; simp [or_comm, or_left_comm]⟩
    · intro he
      obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      obtain ⟨ha, hb⟩ := mem_inter.mp hx
      simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
        mem_singleton, not_or] at ha hb
      simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
        insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
      exact ⟨by simp [Ne.symm ha.1.2], ⟨by simp [hac, Ne.symm ha.1.1], by
        convert ha.2 using 1; ext z; simp [or_comm, or_left_comm]⟩,
        ⟨by simp [hbc, Ne.symm hb.1.1], by
          convert hb.2 using 1; ext z; simp [or_comm, or_left_comm]⟩⟩
  refine ⟨first u v a b c hdistinct hp hn, ?_, ?_⟩
  · have hd' : [u, v, c, b, a].Pairwise (· ≠ ·) := by
      clear first hp hn hk
      simp [List.pairwise_cons] at hdistinct ⊢
      grind
    have hp' : common H {u, v} = ({c, b, a} : Finset V).powersetCard 2 := by
      rw [hp]
      congr 1
      ext z
      simp [or_comm, or_left_comm]
    simpa [pair_comm, inter_comm] using
      first u v c b a hd' hp' (by simpa [pair_comm] using hn)
  · clear first hp hn
    have hd' : (u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ u ≠ c) ∧
        (v ≠ a ∧ v ≠ b ∧ v ≠ c) ∧ (a ≠ b ∧ a ≠ c) ∧ b ≠ c := by
      simpa [List.pairwise_cons] using hdistinct
    obtain ⟨⟨huv, hua, hub, huc⟩, ⟨hva, hvb, hvc⟩, ⟨hab, hac⟩, hbc⟩ := hd'
    ext x
    constructor
    · intro hx
      obtain ⟨ha, hc⟩ := mem_inter.mp hx
      simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
        mem_singleton, not_or] at ha hc
      have hbx : ({b, x} : Finset V) ∈ common H {a, c} := by
        simp only [common, pairs, mem_filter, mem_powersetCard, subset_univ, true_and,
          insert_subset_iff, singleton_subset_iff, neighbors, mem_filter, mem_univ]
        exact ⟨by simp [Ne.symm ha.1.2], ⟨by simp [hab, Ne.symm ha.1.1], by
          convert ha.2 using 1; ext z; simp [or_comm, or_left_comm]⟩,
          ⟨by simp [hbc.symm, Ne.symm hc.1.2], by
            convert hc.2 using 1; ext z; simp [or_comm, or_left_comm]⟩⟩
      rw [hk] at hbx
      simp only [mem_insert, mem_singleton] at hbx
      have hxm : x ∈ ({b, x} : Finset V) := by simp
      rcases hbx with hbx | hbx <;> rw [hbx] at hxm
      · have : x = u := by simpa [ha.1.2] using hxm
        simp [this]
      · have : x = v := by simpa [ha.1.2] using hxm
        simp [this]
    · intro hx
      have hxb : x ≠ b := by
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hbx : ({x, b} : Finset V) ∈ common H {a, c} := by
        rw [hk]
        simp only [mem_insert, mem_singleton] at hx ⊢
        rcases hx with rfl | rfl <;> simp
      have ha := (mem_filter.mp hbx).2 (show a ∈ ({a, c} : Finset V) by simp)
      have hc := (mem_filter.mp hbx).2 (show c ∈ ({a, c} : Finset V) by simp)
      simp only [neighbors, mem_filter, mem_univ, true_and, mem_insert,
        mem_singleton, not_or] at ha hc
      apply mem_inter.mpr
      constructor
      · simp only [neighbors, mem_filter, mem_univ, true_and]
        exact ⟨by simp [Ne.symm ha.1.1, hxb], by simpa [insert_comm] using ha.2⟩
      · simp only [neighbors, mem_filter, mem_univ, true_and]
        exact ⟨by simp [Ne.symm hc.1.1, hxb], by
          convert hc.2 using 1; ext z; simp [or_comm, or_left_comm]⟩

end D5.S3.Combinatorics.Graph.DUFMarkedStars
