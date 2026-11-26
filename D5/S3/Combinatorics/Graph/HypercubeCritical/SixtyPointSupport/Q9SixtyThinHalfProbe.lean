/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyThinHalfProbe
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyThinHalfProbe
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Use the existing small slice obstructions to show that each coordinate half of a sixty-vertex balanced cubic support has at least twenty-two vertices. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyShellCompositionProbe
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointSlice

/-! A sixty-point support has no coordinate half below twenty-two vertices. -/

set_option autoImplicit false

noncomputable section

open SimpleGraph
open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open GirthSliceCounting
open BalancedCriticalSpectrum (Q IsBalanced directionEdges direction_edge_count)
open BalancedCubeLowerBound (coordinateSlice)
attribute [local instance] Classical.propDecidable

open private reindex reindex_regular reindex_balanced reindex_slice from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
open private balanced_subset parity_bipartite paritySide coordinate_slice_degree_cases
  coordinate_slice_low_independent low_slice_card_eq_q parts_card sum_degrees_parts from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound
open private shell thin_half_of_sixty_with_partner_geometry from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport.Q9SixtyShellCompositionProbe

private lemma half_card_lower_bound_sixty {C : Finset (Q 9)}
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (j : Fin 9) (b : Bool) :
    22 ≤ (C.filter (fun x => x j = b)).card := by
  let p := Equiv.swap j (0 : Fin 9)
  let T := C.image (reindex p)
  let S := coordinateSlice T b
  let G := (hypercube 9).induce (S : Set (Q 9))
  have hr' := reindex_regular hr p
  have hb' := reindex_balanced hb p
  have ht : T.card = 60 := by simpa [T,Finset.card_image_of_injective _ (reindex p).injective] using hc
  have hN : S.card = (C.filter (fun x => x j = b)).card := by
    dsimp [S,T,p]
    rw [reindex_slice,Finset.card_image_of_injective _ (reindex _).injective]
  rw [← hN]
  by_contra! hsmall
  by_cases hnineteen : S.card ≤ 19
  · have hT : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨g, pi, hcov, hGray⟩ :=
      NineteenPointSlice.nineteen_point_slice_gray_reconstruction hT hr' hb' b hnineteen
    have hGrayCard : (GrayGridComponent.support 3).card = 54 := by
      simpa using GrayGridComponent.card_support (d := 3) (by decide)
    rw [hGray, Finset.card_image_of_injective _ g.injective, hGrayCard] at ht
    omega
  have hdeg : ∀ v, G.degree v = 2 ∨ G.degree v = 3 :=
    fun v => coordinate_slice_degree_cases v.property hr'
  have h6 : 6 * directionEdges T 0 = 60 := by
    simpa [ht] using direction_edge_count (d := 3) T hr' hb' 0
  have hq' := low_slice_card_eq_q (b := b) hr'
  change (degreeTwo G Finset.univ).card = directionEdges T 0 at hq'
  have hq : (degreeTwo G Finset.univ).card = 10 := by omega
  have hp := parts_card G hdeg Finset.univ
  have hsum : 2 * (degreeTwo G Finset.univ).card +
      3 * (degreeThree G Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_parts G hdeg Finset.univ]
    exact G.sum_degrees_eq_twice_card_edges
  have hcardS : Fintype.card (S : Set (Q 9)) = S.card := by simp
  rw [Finset.card_univ,hcardS,hq] at hp
  rw [hq] at hsum
  have hs20 : S.card = 20 := by omega
  apply TwentyPointSlice.result
  refine ⟨9,S,paritySide S false,paritySide S true,parity_bipartite S,hs20,hdeg,hq,?_,?_⟩
  · intro x y hxy hx hy
    exact coordinate_slice_low_independent hr' hb' hxy hx hy
  · exact balanced_subset hb' (Finset.filter_subset _ _)

private lemma no_sixty_with_partner_geometry (C : Finset (Q 9))
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 7)
    (hpartner : ∀ x ∈ C, ∃ (G : SimpleGraph (Fin 6)) (_ : DecidableRel G.Adj),
      G.edgeFinset.card = (shell C x 7).card ∧
      (∀ v, G.degree v = 0 ∨ G.degree v = 2 ∨ G.degree v = 4) ∧
      G.edgeFinset.card + (Finset.univ.filter (fun v => G.degree v = 2)).card +
        (G.cliqueFinset 3).card ≤ (shell C x 6).card) :
    False := by
  obtain ⟨i,b,hsmall⟩ := thin_half_of_sixty_with_partner_geometry C hc hr hb hdiam hpartner
  have hlarge := half_card_lower_bound_sixty hc hr hb i b
  omega

private lemma no_sixty_of_diameter_le_six (C : Finset (Q 9))
    (hc : C.card = 60)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hdiam : ∀ x ∈ C, ∀ y ∈ C, hammingDist x y ≤ 6) : False := by
  apply no_sixty_with_partner_geometry C hc hr hb
    (fun x hx y hy => (hdiam x hx y hy).trans (by decide))
  intro x hx
  let G : SimpleGraph (Fin 6) := ⊥
  have h0 : shell C x 7 = ∅ := by
    ext y
    simp only [shell,Finset.mem_filter,Finset.notMem_empty,iff_false]
    rintro ⟨hy,he⟩
    have := hdiam x hx y hy
    omega
  have hdeg (v : Fin 6) : G.degree v = 0 := by simp [G]
  have hclique : G.cliqueFinset 3 = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨a,b,c,hab,_,_,_⟩ := SimpleGraph.is3Clique_iff.mp (SimpleGraph.mem_cliqueFinset_iff.mp hs)
    exact hab
  refine ⟨G,inferInstance,?_,fun v => Or.inl (hdeg v),?_⟩
  · simp [G,h0]
  · have ht : (Finset.univ.filter (fun v => G.degree v = 2)).card = 0 := by simp [hdeg]
    rw [ht, hclique, Finset.card_empty, Nat.add_zero]
    apply le_of_eq_of_le ?_ (Nat.zero_le _)
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hm : e ∈ G.edgeSet := (@SimpleGraph.mem_edgeFinset (Fin 6) G e G.fintypeEdgeSet).mp he
    simpa [G] using hm

#print axioms no_sixty_of_diameter_le_six
