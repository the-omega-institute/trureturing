/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion.claim
   digest: The actual symmetric (12,12;4,4) cube slice has no realization. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeLayerDisjointness
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
import D5.S3.Combinatorics.Graph.HypercubeCritical.SixteenCycleExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoEightCycleExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph
import D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle
import Batteries.Tactic.OpenPrivate

/-! Exclusion of the actual symmetric twenty-four-vertex cube slice. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyFourExclusion

open SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

open private degree_parts_union degree_parts_disjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting
open private layerDisjoint from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyFourLayerRegularity
open private High graph side graph_degree side_card actual_partition high_partition
  high_graph_girth from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricHighGraph

open private small_two_regular_cycle from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SmallRegularCycle

private theorem sixteen_two_regular_decomposition
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16) (hdegree : ∀ v, H.degree v = 2)
    (hg : (8 : ℕ∞) ≤ H.egirth) :
    Nonempty (cycleGraph 16 ≃g H) ∨
      ∃ e0 e1 : cycleGraph 8 ↪g H,
        (∀ i j, e0 i ≠ e1 j) ∧
        (∀ v, ∃ i, v = e0 i ∨ v = e1 i) ∧
        (∀ i j, ¬ H.Adj (e0 i) (e1 j)) := by
  classical
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hcycles : H.IsCycles := by
    intro v _
    rw [H.ncard_neighborSet, hdegree]
  have hneighbor (v : V) : (H.neighborSet v).Nonempty := by
    apply (H.degree_pos_iff_nonempty).mp
    rw [hdegree]
    norm_num
  let a : V := Classical.choice inferInstance
  obtain ⟨p, hp, hpc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := H.connectedComponentMk a) (v := a) rfl (hneighbor a)
  have hcomponent (v : V) : H.Reachable a v ↔ v ∈ p.support := by
    rw [← p.mem_verts_toSubgraph, hpc, ConnectedComponent.mem_supp_iff,
      ConnectedComponent.eq]
    exact reachable_comm
  have hp8 : 8 ≤ p.length := by
    exact_mod_cast hg.trans hp.egirth_le_length
  by_cases hcover : ∀ v, v ∈ p.support
  · have hconnected : H.Connected := by
      refine ⟨?_⟩
      intro x y
      exact ((hcomponent x).mpr (hcover x)).symm.trans
        ((hcomponent y).mpr (hcover y))
    have hmax : H.maxDegree ≤ 2 := H.maxDegree_le_of_forall_degree_le 2
      (fun v => by rw [hdegree])
    have hiso := SimpleGraph.cycle_iso_of_connected_degree_le_two H hconnected hmax p hp
    have hlen : p.length = 16 := by
      have hu : p.support.toFinset = (Finset.univ : Finset V) := by
        ext v
        simp [hcover v]
      rw [← hp.support_toFinset_card, hu, Finset.card_univ, hcard]
    exact Or.inl (hlen ▸ hiso)
  · obtain ⟨b, hb⟩ := not_forall.mp hcover
    obtain ⟨q, hq, hqc⟩ := hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (c := H.connectedComponentMk b) (v := b) rfl (hneighbor b)
    have hq8 : 8 ≤ q.length := by
      exact_mod_cast hg.trans hq.egirth_le_length
    have hdis : Disjoint p.support.toFinset q.support.toFinset := by
      apply Finset.disjoint_left.mpr
      intro w hwp hwq
      have hwpr := (hcomponent w).mpr (List.mem_toFinset.mp hwp)
      have hwqr : H.Reachable b w := by
        obtain ⟨r, s, _⟩ := q.mem_support_iff_exists_append.mp (List.mem_toFinset.mp hwq)
        exact r.reachable
      exact hb ((hcomponent b).mp (hwpr.trans hwqr.symm))
    have hsum : p.length + q.length ≤ 16 := by
      have hle := Finset.card_le_card
        (Finset.subset_univ (p.support.toFinset ∪ q.support.toFinset))
      rw [Finset.card_union_of_disjoint hdis,
        hp.support_toFinset_card, hq.support_toFinset_card, Finset.card_univ, hcard] at hle
      exact hle
    have hplen : p.length = 8 := by omega
    have hqlen : q.length = 8 := by omega
    have hunion : p.support.toFinset ∪ q.support.toFinset = (Finset.univ : Finset V) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdis,
        hp.support_toFinset_card, hq.support_toFinset_card, Finset.card_univ, hcard,
        hplen, hqlen]
    have component_embedding (c : H.ConnectedComponent) (hc : Fintype.card c.supp = 8) :
        ∃ e : cycleGraph 8 ↪g H, ∀ v, (∃ i, e i = v) ↔ v ∈ c.supp := by
      let K : SimpleGraph c.supp := H.induce c.supp
      let : Nonempty c.supp := Fintype.card_pos_iff.mp (by omega)
      have hKdegree (x : c.supp) : K.degree x = 2 := by
        have hsub : H.neighborSet x.val ⊆ c.supp := by
          intro y hxy
          exact (c.mem_supp_congr_adj hxy).mp x.property
        exact (H.degree_induce_of_neighborSet_subset hsub).trans (hdegree x.val)
      have hKg : (8 : ℕ∞) ≤ K.egirth :=
        hg.trans (SimpleGraph.Embedding.induce c.supp).isContained.egirth_le
      obtain ⟨u, r, _hr, hlen, _hcover, hiso⟩ :=
        small_two_regular_cycle K hKdegree hKg (by omega)
      have hl : r.length = 8 := hlen.trans hc
      have hi : Nonempty (cycleGraph 8 ≃g K) := hl ▸ hiso
      obtain ⟨e⟩ := hi
      let f : cycleGraph 8 ↪g H :=
        { toFun := fun i => (e i).val
          inj' := fun i j he => e.injective (Subtype.ext he)
          map_rel_iff' := by intro i j; exact e.map_rel_iff }
      refine ⟨f, ?_⟩
      intro v
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro hv
        let y : c.supp := ⟨v, hv⟩
        refine ⟨e.symm y, ?_⟩
        change (e (e.symm y)).val = v
        simp [y]
    have hP : Fintype.card (H.connectedComponentMk a).supp = 8 := by
      rw [← Set.toFinset_card]
      have he : (H.connectedComponentMk a).supp.toFinset = p.support.toFinset := by
        ext v
        simp only [Set.mem_toFinset, List.mem_toFinset]
        rw [← hpc, p.mem_verts_toSubgraph]
      rw [he, hp.support_toFinset_card, hplen]
    have hQ : Fintype.card (H.connectedComponentMk b).supp = 8 := by
      rw [← Set.toFinset_card]
      have he : (H.connectedComponentMk b).supp.toFinset = q.support.toFinset := by
        ext v
        simp only [Set.mem_toFinset, List.mem_toFinset]
        rw [← hqc, q.mem_verts_toSubgraph]
      rw [he, hq.support_toFinset_card, hqlen]
    obtain ⟨e0, he0⟩ := component_embedding (H.connectedComponentMk a) hP
    obtain ⟨e1, he1⟩ := component_embedding (H.connectedComponentMk b) hQ
    have he0p (i : Fin 8) : e0 i ∈ p.support := by
      rw [← p.mem_verts_toSubgraph, hpc]
      exact (he0 _).mp ⟨i, rfl⟩
    have he1q (i : Fin 8) : e1 i ∈ q.support := by
      rw [← q.mem_verts_toSubgraph, hqc]
      exact (he1 _).mp ⟨i, rfl⟩
    refine Or.inr ⟨e0, e1, ?_, ?_, ?_⟩
    · intro i j hij
      exact Finset.disjoint_left.mp hdis
        (List.mem_toFinset.mpr (hij ▸ he0p i))
        (List.mem_toFinset.mpr (he1q j))
    · intro v
      have hv : v ∈ p.support.toFinset ∪ q.support.toFinset := by
        rw [hunion]
        exact Finset.mem_univ v
      rcases Finset.mem_union.mp hv with hv | hv
      · have hc : v ∈ (H.connectedComponentMk a).supp := by
          rw [← hpc, p.mem_verts_toSubgraph]
          exact List.mem_toFinset.mp hv
        obtain ⟨i, hi⟩ := (he0 v).mpr hc
        exact ⟨i, Or.inl hi.symm⟩
      · have hc : v ∈ (H.connectedComponentMk b).supp := by
          rw [← hqc, q.mem_verts_toSubgraph]
          exact List.mem_toFinset.mp hv
        obtain ⟨i, hi⟩ := (he1 v).mpr hc
        exact ⟨i, Or.inr hi.symm⟩
    · intro i j hij
      have hc := ((H.connectedComponentMk a).mem_supp_congr_adj hij).mp
        ((he0 _).mp ⟨i, rfl⟩)
      have hpj : e1 j ∈ p.support := by
        rw [← p.mem_verts_toSubgraph, hpc]
        exact hc
      exact Finset.disjoint_left.mp hdis
        (List.mem_toFinset.mpr hpj) (List.mem_toFinset.mpr (he1q j))

open Classical in
def claim : Prop :=
  ∃ m n : ℕ, ∃ G : SimpleGraph (Fin m), ∃ L R : Finset (Fin m),
    ∃ f : Fin m → (Fin n → Bool),
      Function.Injective f ∧
      (∀ a b, G.Adj a b ↔ (hypercube n).Adj (f a) (f b)) ∧
      G.IsBipartiteWith (L : Set (Fin m)) (R : Set (Fin m)) ∧
      L.card = 12 ∧ R.card = 12 ∧
      (∀ v, G.degree v = 2 ∨ G.degree v = 3) ∧
      (degreeTwo G L).card = 4 ∧ (degreeTwo G R).card = 4 ∧
      (∀ {v w}, G.Adj v w → G.degree v = 2 → G.degree w = 2 → False) ∧
      (8 : ℕ∞) ≤ G.egirth

theorem result : ¬ claim := by
  classical
  rintro ⟨m, n, G, L, R, f, hf, hind, hpart, hL, hR, hdeg, hL2, hR2, hlow, hg⟩
  have hD : layerDisjoint G := by
    intro x y z hyz hxy hxz hy hz hny hnz
    have hcover := actual_partition hpart hdeg x
    have root_disjoint {L' R' : Finset (Fin m)}
        (hpart' : G.IsBipartiteWith (L' : Set (Fin m)) (R' : Set (Fin m)))
        (hx' : x ∈ L') : Disjoint (G.neighborFinset y) (G.neighborFinset z) := by
      apply Finset.disjoint_left.mpr
      intro w hwy hwz
      apply CubeLayerDisjointness.result
      refine ⟨n, m, G, f, L', R', x, y, z, w, hf, hind, hpart', hx', hg,
        hxy, hxz, hy, hz, ?_, ?_, hyz,
        (G.mem_neighborFinset _ _).mp hwy, (G.mem_neighborFinset _ _).mp hwz⟩
      · intro u hu
        exact hny u ((G.mem_neighborFinset _ _).mpr hu)
      · intro u hu
        exact hnz u ((G.mem_neighborFinset _ _).mpr hu)
    rcases hcover with hxL | hxR
    · exact root_disjoint hpart hxL
    · exact root_disjoint hpart.symm hxR
  have hreg : ∀ v, G.degree v = 3 →
      (degreeThree G (G.neighborFinset v)).card = 2 := by
    intro v hv
    by_contra hn
    exact TwentyFourLayerRegularity.result
      ⟨m, G, L, R, hpart, hL, hR, hdeg, hL2, hR2, hlow, hg, hD, v, hv, hn⟩
  obtain ⟨hd, hu, _hKpart⟩ := high_partition hpart hdeg
  have hL3 : (degreeThree G L).card = 8 := by
    have h := congrArg Finset.card (degree_parts_union hdeg L)
    rw [Finset.card_union_of_disjoint (degree_parts_disjoint _), hL2, hL] at h
    omega
  have hR3 : (degreeThree G R).card = 8 := by
    have h := congrArg Finset.card (degree_parts_union hdeg R)
    rw [Finset.card_union_of_disjoint (degree_parts_disjoint _), hR2, hR] at h
    omega
  have hsL : (side G L).card = 8 := (side_card G L).trans hL3
  have hsR : (side G R).card = 8 := (side_card G R).trans hR3
  have hc := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint hd, hsL, hsR, Finset.card_univ] at hc
  have hKcard : Fintype.card (High G) = 16 := hc.symm
  have hKg : (8 : ℕ∞) ≤ (graph G).egirth := high_graph_girth hg
  have hKdegree : ∀ x : High G, (graph G).degree x = 2 := by
    intro x
    rw [graph_degree]
    exact hreg x.val x.property
  obtain hdec := sixteen_two_regular_decomposition (graph G) hKcard hKdegree hKg
  rcases hdec with ⟨⟨e⟩⟩ | ⟨e0, e1, hdis, hcover, hcross⟩
  · apply SixteenCycleExclusion.result
    refine ⟨m, G, L, R, hpart, hdeg, hlow, hg, (fun i => (e i).val), ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact e.injective (Subtype.ext hij)
    · intro i
      exact (e i).property
    · intro i j
      simpa [graph] using (e.map_adj_iff :
        (graph G).Adj (e i) (e j) ↔ (cycleGraph 16).Adj i j)
    · intro v hv
      refine ⟨e.symm ⟨v, hv⟩, ?_⟩
      change (e (e.symm ⟨v, hv⟩)).val = v
      simp
  · apply TwoEightCycleExclusion.result
    refine ⟨m, n, G, L, R, f, (fun i => (e0 i).val), (fun i => (e1 i).val),
      hf, hind, hpart, hdeg, hlow, hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro i j hij
        exact e0.injective (Subtype.ext hij)
      · intro i j hij
        exact e1.injective (Subtype.ext hij)
    · intro i j hij
      exact hdis i j (Subtype.ext hij)
    · intro i
      exact (e0 i).property
    · intro i
      exact (e1 i).property
    · intro v hv
      obtain ⟨i, hi | hi⟩ := hcover ⟨v, hv⟩
      · exact ⟨i, Or.inl (congrArg Subtype.val hi)⟩
      · exact ⟨i, Or.inr (congrArg Subtype.val hi)⟩
    · intro i j
      simpa [graph] using (e0.map_adj_iff :
        (graph G).Adj (e0 i) (e0 j) ↔ (cycleGraph 8).Adj i j)
    · intro i j
      simpa [graph] using (e1.map_adj_iff :
        (graph G).Adj (e1 i) (e1 j) ↔ (cycleGraph 8).Adj i j)
    · intro i j hij
      exact hcross i j hij

#print axioms result

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricTwentyFourExclusion
