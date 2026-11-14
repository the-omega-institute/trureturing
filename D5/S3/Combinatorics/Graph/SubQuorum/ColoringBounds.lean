/- GID: D5/S3/Combinatorics/Graph/SubQuorum/ColoringBounds
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/ColoringBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: A degree-three vertex excludes a fully injective sub-quorum coloring. -/

import D5.S3.Combinatorics.Graph.SubQuorum.DoubleStarGrafting

/-! The general form of the complete certificate note's six-color exclusion.
The actual support and palette are those already used by double-star grafting. -/

set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Combinatorics.Graph.SubQuorum.ColoringBounds

open DoubleStarGrafting

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- A represented color at every vertex would force full support and injectivity;
a vertex with at least three neighbors then violates the closed-neighborhood majority. -/
theorem palette_lt_card_of_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hd : 3 ≤ (Finset.univ.filter (G.Adj v)).card)
    (c : V → Option C) (hc : IsSubQuorum G c) :
    (palette c Finset.univ).card < Fintype.card V := by
  classical
  by_contra h
  have hp : Fintype.card V ≤ (palette c Finset.univ).card := by omega
  have hi := Finset.card_image_le (s := coloredSupport c Finset.univ) (f := c)
  have hsupport : coloredSupport c Finset.univ = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    dsimp [palette] at hp
    simpa only [coloredSupport, Finset.card_univ] using hp.trans hi
  have hinj : Set.InjOn c (coloredSupport c Finset.univ) :=
    Finset.injOn_of_card_image_eq (by
      dsimp [palette] at hp
      rw [hsupport] at hp hi ⊢
      simp only [Finset.card_univ] at hi ⊢
      omega)
  have hcol (w : V) : c w ≠ none := by
    have hw : w ∈ coloredSupport c Finset.univ := by rw [hsupport]; simp
    exact (Finset.mem_filter.mp hw).2
  have hsame : ((Finset.univ.filter (G.Adj v)).filter (fun w => c w = c v)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro w hw he
    have hwv : w = v := hinj (by rw [hsupport]; simp) (by rw [hsupport]; simp) he
    exact G.irrefl (hwv ▸ (Finset.mem_filter.mp hw).2)
  have hcolored : ((Finset.univ.filter (G.Adj v)).filter (fun w => c w ≠ none)) =
      Finset.univ.filter (G.Adj v) := by
    ext w
    simp [hcol]
  have hgood := hc v (hcol v)
  have hN : @Finset.filter V (G.Adj v) (fun w => Classical.propDecidable _) Finset.univ =
      Finset.univ.filter (G.Adj v) := by ext w; simp
  rw [hN, hsame, hcolored] at hgood
  simp only [Finset.card_empty] at hgood
  omega

end D5.S3.Combinatorics.Graph.SubQuorum.ColoringBounds
