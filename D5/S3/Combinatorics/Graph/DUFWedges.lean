/- GID: D5/S3/Combinatorics/Graph/DUFWedges
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFWedges
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/DUFStructure]
   utility: none
   digest: Unordered wedges in exact four-neighborhood fibers correspond to four-edge common links. -/

import D5.S3.Combinatorics.Graph.DUFStructure
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFWedges

open Finset DUFStructure
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices in the union but not the intersection of an unordered edge family. -/
def tips (w : Finset (Finset V)) : Finset V :=
  w.biUnion id \ univ.filter (fun x => ∀ p ∈ w, x ∈ p)

/-- An unordered wedge is indexed once by its exact four-neighborhood. -/
def wedges (H : Finset (Finset V)) : Finset (Σ _ : Finset V, Finset (Finset V)) :=
  (univ.powersetCard 4).sigma fun S => (fiber H S).powersetCard 2

/-- Each unordered wedge yields a four-edge common link with the same center. -/
theorem wedge_structure (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (S : Finset V) (hS : S.card = 4) (w : Finset (Finset V))
    (hw : w ∈ (fiber H S).powersetCard 2) :
    ∃ c q, c ∉ q ∧ c ∉ S ∧ q.card = 2 ∧ w = star c q ∧ tips w = q ∧
      common H q = star c S ∧ (common H q).card = 4 := by
  obtain ⟨hwF, hw2⟩ := mem_powersetCard.mp hw
  have hi : Intersecting w := fun p hp r hr => (fiber_structure H hd hc S hS).2.1
    p (hwF hp) r (hwF hr)
  have hp : ∀ p ∈ w, p.card = 2 := by
    intro p hp
    exact (mem_powersetCard.mp (mem_filter.mp (hwF hp)).1).2
  rcases intersecting_classification w hp hi (card_pos.mp (by omega)) with
    ⟨c, q, hcq, he, hq⟩ | ⟨T, hT, he⟩
  · have hq2 : q.card = 2 := hq.trans hw2
    have hn (u : V) (hu : u ∈ q) : neighbors H {c, u} = S := by
      have hem : ({c, u} : Finset V) ∈ w := by
        rw [he]; exact mem_image.mpr ⟨u, hu, rfl⟩
      exact (mem_filter.mp (hwF hem)).2
    have hcs : c ∉ S := by
      obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < q.card)
      intro hcs
      have : c ∈ neighbors H {c, u} := (hn u hu).symm ▸ hcs
      simp [neighbors] at this
    have hsub : star c S ⊆ common H q := by
      intro e he'
      obtain ⟨s, hs, rfl⟩ := mem_image.mp he'
      have hsc : c ≠ s := by intro h; subst c; exact hcs hs
      refine mem_filter.mpr ⟨by simp [pairs, hsc], ?_⟩
      intro u hu
      have hm : s ∈ neighbors H {c, u} := (hn u hu).symm ▸ hs
      simp only [neighbors, mem_filter, mem_univ, true_and] at hm ⊢
      have huc : u ≠ c := by intro h; subst u; exact hcq hu
      have hus : u ≠ s := by intro h; subst u; exact hm.1 (by simp)
      exact ⟨by simp [huc, hus], by simpa [insert_comm, pair_comm] using hm.2⟩
    have hstar : (star c S).card = 4 := by
      rw [DUFStructure.star, card_image_iff.mpr, hS]
      intro a ha b hb hab
      have hac : a ≠ c := by intro h; subst a; exact hcs ha
      have : a ∈ ({c, b} : Finset V) := by
        change ({c, a} : Finset V) = {c, b} at hab
        rw [← hab]; simp
      simpa [hac] using this
    have hK : common H q = star c S :=
      (eq_of_subset_of_card_le hsub (by
        rw [hstar]; exact (common_structure H hd hc q hq2).1)).symm
    refine ⟨c, q, hcq, hcs, hq2, he, ?_, hK, by rw [hK, hstar]⟩
    obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hq2
    have hcu : c ≠ u := by intro h; exact hcq (by simp [h])
    have hcv : c ≠ v := by intro h; exact hcq (by simp [h])
    rw [he]
    ext x
    simp [tips, DUFStructure.star]
    grind
  · have : w.card = 3 := by rw [he, card_powersetCard, hT]; decide
    omega

/-- The two tips give a bijection, with no orientation of either a wedge or a pair. -/
theorem wedge_bijection (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H) :
    Set.BijOn (fun w : Σ _ : Finset V, Finset (Finset V) => tips w.2)
      (wedges H) (pairs.filter fun q => (common H q).card = 4) ∧
    (pairs.filter fun q => (common H q).card = 4).card =
      ∑ S ∈ univ.powersetCard 4, ((fiber H S).card).choose 2 := by
  have hpair (c : V) : Function.Injective (fun a : V => ({c, a} : Finset V)) := by
    intro a b hab
    change ({c, a} : Finset V) = {c, b} at hab
    have h1 : a = c ∨ a = b := by
      have : a ∈ ({c, b} : Finset V) := by rw [← hab]; simp
      simpa only [mem_insert, mem_singleton] using this
    have h2 : b = c ∨ b = a := by
      have : b ∈ ({c, a} : Finset V) := by rw [hab]; simp
      simpa only [mem_insert, mem_singleton] using this
    grind
  have hm (w : Σ _ : Finset V, Finset (Finset V)) (hw : w ∈ wedges H) :
      ∃ c, c ∉ tips w.2 ∧ c ∉ w.1 ∧ (tips w.2).card = 2 ∧
        w.2 = star c (tips w.2) ∧ common H (tips w.2) = star c w.1 ∧
        (common H (tips w.2)).card = 4 := by
    obtain ⟨hS, hw⟩ := mem_sigma.mp hw
    obtain ⟨c, q, hcq, hcs, hq, he, ht, hk, h4⟩ :=
      wedge_structure H hd hc w.1 (mem_powersetCard.mp hS).2 w.2 hw
    exact ⟨c, ht.symm ▸ hcq, hcs, ht.symm ▸ hq, ht.symm ▸ he,
      ht.symm ▸ hk, ht.symm ▸ h4⟩
  have hmap : Set.MapsTo (fun w : Σ _ : Finset V, Finset (Finset V) => tips w.2)
      (wedges H) (pairs.filter fun q => (common H q).card = 4) := by
    intro w hw
    obtain ⟨c, _, _, hq, _, _, h4⟩ := hm w hw
    exact mem_filter.mpr ⟨by simp [pairs, hq], h4⟩
  have hinj : Set.InjOn (fun w : Σ _ : Finset V, Finset (Finset V) => tips w.2)
      (wedges H) := by
    intro w hw z hz ht
    obtain ⟨c, hcq, hcs, hq, he, hk, _⟩ := hm w hw
    obtain ⟨d, hdq, hdt, _, he', hk', _⟩ := hm z hz
    have hstars : star c w.1 = star d z.1 := hk.symm.trans ((congrArg (common H) ht).trans hk')
    have hcd : c = d := by
      by_contra hcd
      have hsub : w.1 ⊆ {d} := by
        intro s hs
        have hem : ({c, s} : Finset V) ∈ star d z.1 := by
          rw [← hstars]; exact mem_image.mpr ⟨s, hs, rfl⟩
        obtain ⟨t, _, het⟩ := mem_image.mp hem
        have hdm : d ∈ ({c, s} : Finset V) := by rw [← het]; simp
        exact mem_singleton.mpr (by simpa [Ne.symm hcd] using hdm : d = s).symm
      have h4 := (mem_powersetCard.mp (mem_sigma.mp hw).1).2
      have := card_le_card hsub
      simp only [card_singleton] at this
      omega
    subst d
    have hST : w.1 = z.1 := image_injective (hpair c) hstars
    have hwz : w.2 = z.2 := he.trans ((congrArg (star c) ht).trans he'.symm)
    exact Sigma.ext hST (heq_of_eq hwz)
  have hsurj : Set.SurjOn (fun w : Σ _ : Finset V, Finset (Finset V) => tips w.2)
      (wedges H) (pairs.filter fun q => (common H q).card = 4) := by
    intro q hq
    obtain ⟨hqP, h4⟩ := mem_filter.mp hq
    have hq2 := (mem_powersetCard.mp hqP).2
    obtain ⟨c, S, hcq, hcs, hS, hk, hn⟩ := (common_structure H hd hc q hq2).2 h4
    have hw : star c q ∈ (fiber H S).powersetCard 2 := by
      apply mem_powersetCard.mpr
      constructor
      · intro e he
        obtain ⟨u, hu, rfl⟩ := mem_image.mp he
        have hcu : c ≠ u := by intro h; subst c; exact hcq hu
        exact mem_filter.mpr ⟨by simp [pairs, hcu], hn u hu⟩
      · rw [DUFStructure.star, card_image_of_injective _ (hpair c), hq2]
    refine ⟨⟨S, star c q⟩, mem_sigma.mpr ⟨by simp [hS], hw⟩, ?_⟩
    change tips (star c q) = q
    obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hq2
    have hcu : c ≠ u := by intro h; exact hcq (by simp [h])
    have hcv : c ≠ v := by intro h; exact hcq (by simp [h])
    ext x
    simp [tips, DUFStructure.star]
    grind
  refine ⟨⟨hmap, hinj, hsurj⟩, ?_⟩
  rw [← card_nbij _ hmap hinj hsurj, wedges, card_sigma]
  simp only [card_powersetCard]

end D5.S3.Combinatorics.Graph.DUFWedges
