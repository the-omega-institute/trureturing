/- GID: D5/S3/Combinatorics/SignedDoubleRoman/SubcubicThreeColouring
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SignedDoubleRoman/SubcubicThreeColouring
   mirror-E: none(waiver:elementary-subcubic-colouring)
   anchors: []
   utility: none
   digest: Every finite subcubic graph without a four-clique has a proper three-colouring. -/

import D5.S3.Combinatorics.SignedDoubleRoman.PairConnectivity

set_option autoImplicit false

namespace D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The connected case separates deficient vertices, single cuts and double cuts. -/
theorem colorable_of_preconnected_subcubic (hconn : G.Preconnected)
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3) (hclique : G.CliqueFree 4) :
    G.Colorable 3 := by
  classical
  by_cases hdef : ∃ r, (G.neighborFinset r).card ≤ 2
  · obtain ⟨r, hr⟩ := hdef
    exact colorable_of_preconnected_deficient G hconn hdeg r hr
  have hcubic : ∀ r, (G.neighborFinset r).card = 3 := by
    intro r
    have := hdeg r
    have hh : ¬(G.neighborFinset r).card ≤ 2 := fun h => hdef ⟨r, h⟩
    omega
  by_cases hcut : ∃ r, ¬(G.induce {v | v ≠ r}).Preconnected
  · obtain ⟨r, hr⟩ := hcut
    exact colorable_of_cut_vertex G hconn hdeg r hr
  have hsingle : ∀ r, (G.induce {v | v ≠ r}).Preconnected := by
    intro r
    by_contra h
    exact hcut ⟨r, h⟩
  by_cases hpairs : ∀ x y, x ≠ y → (G.induce ({x, y} : Set V)ᶜ).Preconnected
  · exact colorable_of_pair_deletions_preconnected G hconn hdeg hclique hpairs
  push Not at hpairs
  obtain ⟨x, y, hxy, hbad⟩ := hpairs
  have hbad' : ¬(G.induce {v | v ≠ x ∧ v ≠ y}).Preconnected := by
    have hs : {v | v ≠ x ∧ v ≠ y} = ({x, y} : Set V)ᶜ := by ext v; simp
    rwa [hs]
  obtain ⟨a, b, hab, hxa, hxb, hnab, hpair⟩ :=
    exists_nonseparating_neighbours G hsingle hcubic x y hxy hbad'
  exact colorable_of_preconnected_pair G hdeg x a b hab hnab hxa hxb hpair

/-- Colour the connected components independently using the elementary connected proof. -/
theorem colorable_of_subcubic_cliqueFree
    (hdeg : ∀ v, (G.neighborFinset v).card ≤ 3) (hclique : G.CliqueFree 4) :
    G.Colorable 3 := by
  classical
  apply G.colorable_iff_forall_connectedComponent.mpr
  intro c
  have hsmall : ∀ v : c, (c.toSimpleGraph.neighborFinset v).card ≤ 3 := by
    intro v
    have hsub : (c.toSimpleGraph.neighborFinset v).image Subtype.val ⊆
        G.neighborFinset v.val := by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      have hadj : c.toSimpleGraph.Adj v z := by simpa using hz
      simpa using (show G.Adj v.val z.val from hadj)
    have hh := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
    exact hh.trans (hdeg v.val)
  have hfree : c.toSimpleGraph.CliqueFree 4 :=
    SimpleGraph.CliqueFree.comap (SimpleGraph.Embedding.induce c.supp).isContained hclique
  exact colorable_of_preconnected_subcubic c.toSimpleGraph
    c.connected_toSimpleGraph.preconnected hsmall hfree

#print axioms colorable_of_subcubic_cliqueFree

end D5.S3.Combinatorics.SignedDoubleRoman.SubcubicColouring
