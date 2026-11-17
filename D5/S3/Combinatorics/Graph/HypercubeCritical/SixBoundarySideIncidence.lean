/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Private actual edge and middle labels for the auxiliary cube. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideLabeling

/-! The constructive cube labeling determines the original left labels and the
degree-two middles that pair antipodal parallel edges. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap

open scoped BigOperators Classical
open SimpleGraph GirthSliceCounting
attribute [local instance] Classical.propDecidable
open private sideCore edgeLabels high_core_third low_partner
  partner_no_shared_high partner_no_cross_edge from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideCore
open private cubeEightNeighbors from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideLabeling

private def cubeEdgeFrom : Fin 12 → Fin 8 := ![0,1,6,5,4,3,0,2,2,1,7,7]
private def cubeEdgeTo : Fin 12 → Fin 8 := ![1,6,5,4,3,0,2,6,4,7,5,3]
private def cubeEdgeEnds (j : Fin 12) : Finset (Fin 8) := {cubeEdgeFrom j, cubeEdgeTo j}
private def cubeEdgeOpposite : Fin 12 → Fin 12 := ![3,4,5,0,1,2,10,11,9,8,6,7]
private def firstThreeEdges (i : Fin 3) : Fin 12 := ⟨i.val, by omega⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {L R : Finset V}

private theorem cube_edge_labels
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hleft : ∀ x ∈ L, (degreeThree G (G.neighborFinset x)).card = 2)
    (hL : L.card = 12)
    (v : Fin 8 → (degreeThree G R : Set V)) (hv : Function.Bijective v)
    (hN : ∀ i z, (sideCore G L R).Adj (v i) z ↔ z ∈ (cubeEightNeighbors i).image v) :
    ∃ e : Fin 12 → V, Function.Injective e ∧ (∀ j, e j ∈ L) ∧
      (∀ x ∈ L, ∃ j, e j = x) ∧
      ∀ i j, G.Adj (v i).val (e j) ↔ i ∈ cubeEdgeEnds j := by
  have he (j : Fin 12) : (sideCore G L R).Adj (v (cubeEdgeFrom j)) (v (cubeEdgeTo j)) := by
    apply (hN _ _).mpr
    exact Finset.mem_image.mpr ⟨cubeEdgeTo j, (by
      have h : ∀ j, cubeEdgeTo j ∈ cubeEightNeighbors (cubeEdgeFrom j) := by decide
      exact h j), rfl⟩
  have hex (j : Fin 12) : ∃ x ∈ L,
      G.Adj (v (cubeEdgeFrom j)).val x ∧ G.Adj (v (cubeEdgeTo j)).val x ∧
      degreeThree G (G.neighborFinset x) =
        {(v (cubeEdgeFrom j)).val, (v (cubeEdgeTo j)).val} := by
    obtain ⟨hne, x, hx, hax, hbx⟩ := he j
    have hxL := (Finset.mem_filter.mp hx).1
    refine ⟨x, hxL, hax, hbx, ?_⟩
    apply (Finset.eq_of_subset_of_card_le (by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hax.symm,
        (Finset.mem_filter.mp (v (cubeEdgeFrom j)).property).2⟩,
        Finset.mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hbx.symm,
        (Finset.mem_filter.mp (v (cubeEdgeTo j)).property).2⟩⟩) ?_).symm
    have hn : (v (cubeEdgeFrom j)).val ≠ (v (cubeEdgeTo j)).val :=
      fun h => hne (Subtype.ext h)
    simp [hleft x hxL, hn]
  let e (j : Fin 12) := Classical.choose (hex j)
  have hs (j : Fin 12) := Classical.choose_spec (hex j)
  have hi (i : Fin 8) (j : Fin 12) : G.Adj (v i).val (e j) ↔ i ∈ cubeEdgeEnds j := by
    have hvval : Function.Injective (fun i => (v i).val) := by
      intro i k h; exact hv.1 (Subtype.ext h)
    have hm : G.Adj (v i).val (e j) ↔
        (v i).val ∈ degreeThree G (G.neighborFinset (e j)) := by
      simp only [degreeThree, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => ⟨h.symm, (Finset.mem_filter.mp (v i).property).2⟩,
        fun h => h.1.symm⟩
    rw [hm, (hs j).2.2.2]
    simp only [cubeEdgeEnds, Finset.mem_insert, Finset.mem_singleton, hvval.eq_iff]
  have hinj : Function.Injective e := by
    intro j k hjk
    have hh : cubeEdgeEnds j = cubeEdgeEnds k := by
      ext i
      rw [← hi i j, ← hi i k, hjk]
    have h : Function.Injective cubeEdgeEnds := by decide
    exact h hh
  have hcover : ∀ x ∈ L, ∃ j, e j = x := by
    have hE : Finset.univ.image e = L := by
      apply Finset.eq_of_subset_of_card_le (by
        intro x hx; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx; exact (hs j).1)
      rw [Finset.card_image_of_injective _ hinj]
      simp [hL]
    intro x hx
    rw [← hE] at hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    exact ⟨j, hj⟩
  exact ⟨e, hinj, fun j => (hs j).1, hcover, hi⟩

private theorem cube_opposite_forced (j k : Fin 12)
    (hsep : ∀ s ∈ cubeEdgeEnds j, ∀ t ∈ cubeEdgeEnds k,
      s ≠ t ∧ t ∉ cubeEightNeighbors s) : k = cubeEdgeOpposite j := by
  have h : ∀ j k : Fin 12,
      (∀ s ∈ cubeEdgeEnds j, ∀ t ∈ cubeEdgeEnds k,
        s ≠ t ∧ t ∉ cubeEightNeighbors s) → k = cubeEdgeOpposite j := by decide
  exact h j k hsep

private theorem cube_low_middles
    (hb : G.IsBipartiteWith (L : Set V) (R : Set V))
    (hg : (8 : ℕ∞) ≤ G.egirth)
    (hd : ∀ x ∈ L, G.degree x = 3)
    (hr : ∀ y ∈ R, G.degree y = 2 ∨ G.degree y = 3)
    (hleft : ∀ x ∈ L, (degreeThree G (G.neighborFinset x)).card = 2)
    (v : Fin 8 → (degreeThree G R : Set V)) (hv : Function.Bijective v)
    (hN : ∀ i z, (sideCore G L R).Adj (v i) z ↔ z ∈ (cubeEightNeighbors i).image v)
    (e : Fin 12 → V) (heL : ∀ j, e j ∈ L)
    (hecover : ∀ x ∈ L, ∃ j, e j = x)
    (hinc : ∀ i j, G.Adj (v i).val (e j) ↔ i ∈ cubeEdgeEnds j) :
    ∃ m : Fin 3 → V, (∀ i, m i ∈ degreeTwo G R) ∧
      ∀ i, G.neighborFinset (m i) =
        {e (firstThreeEdges i), e (cubeEdgeOpposite (firstThreeEdges i))} := by
  have hex (j : Fin 12) : ∃ m ∈ degreeTwo G R,
      G.neighborFinset m = {e j, e (cubeEdgeOpposite j)} := by
    have hj : e j ∈ edgeLabels G L := Finset.mem_filter.mpr ⟨heL j, hleft _ (heL j)⟩
    obtain ⟨m, hm, f, hf, hfe, hem, hfm, hmf⟩ := low_partner hb hd hr hj
    obtain ⟨k, rfl⟩ := hecover f hf
    have hkj : k = cubeEdgeOpposite j := by
      apply cube_opposite_forced
      intro s hs t ht
      have hse := (hinc s j).mpr hs
      have htf := (hinc t k).mpr ht
      refine ⟨?_, ?_⟩
      · intro hst
        exact partner_no_shared_high hb hg (heL j) hfe.symm
          (Finset.mem_filter.mp hm).2 hem hfm (v s) hse (hst ▸ htf)
      · intro hst
        have hcore : (sideCore G L R).Adj (v s) (v t) := by
          apply (hN _ _).mpr
          exact Finset.mem_image.mpr ⟨t, hst, rfl⟩
        exact partner_no_cross_edge hb hg (heL j) hfe.symm
          (Finset.mem_filter.mp hm).2 hem hfm (v s) (v t) hse htf hcore
    exact ⟨m, hm, hkj ▸ hmf⟩
  let m (i : Fin 3) := Classical.choose (hex (firstThreeEdges i))
  exact ⟨m, fun i => (Classical.choose_spec (hex (firstThreeEdges i))).1,
    fun i => (Classical.choose_spec (hex (firstThreeEdges i))).2⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.SixBoundarySideGap
