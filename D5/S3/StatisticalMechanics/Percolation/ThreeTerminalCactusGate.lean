/- GID: D5/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Percolation/ThreeTerminalCactusGate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Deleting a cactus cycle leaves a unique gate on that cycle in each component. -/

import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusSharpness
import D5.S3.StatisticalMechanics.Percolation.ThreeTerminalGluing

/-! A cycle separates a cactus into pieces with one attachment vertex each. -/

namespace D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
open SimpleGraph
open ThreeTerminalCactusSharpness

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

private theorem cycle_vertices_separated (hG : IsCactus G) {o x y : V}
    (C : G.Walk o o) (hC : C.IsCycle) (hx : x ∈ C.support) (hy : y ∈ C.support)
    (hxy : (G.deleteEdges C.edgeSet).Reachable x y) : x = y := by
  by_contra hne
  obtain ⟨r, hr⟩ := hxy.exists_isPath
  let p := r.mapLe (G.deleteEdges_le C.edgeSet)
  have hp : p.IsPath := hr.mapLe _
  have hpout : ∀ e ∈ p.edges, e ∉ C.edges := by
    intro e he
    have hh := r.edges_subset_edgeSet (by simpa [p] using he)
    rw [edgeSet_deleteEdges] at hh
    exact hh.2
  let D := C.rotate x hx
  have hD : D.IsCycle := hC.rotate hx
  have hyD : y ∈ D.support := (C.mem_support_rotate_iff x hx).2 hy
  let q := D.takeUntil y hyD
  have hq : q.IsPath := hD.isPath_takeUntil hyD
  have hqsupp : ∀ z ∈ q.support, z ∈ C.support := by
    intro z hz
    exact (C.mem_support_rotate_iff x hx).1 (D.support_takeUntil_subset_support hyD hz)
  have hqedges : ∀ e ∈ q.edges, e ∈ C.edges := by
    intro e he
    exact (C.rotate_edges x hx).mem_iff.mp (D.edges_takeUntil_subset_edges hyD he)
  have hpq : p ≠ q := by
    intro heq
    have he := p.mk_start_snd_mem_edges (Walk.not_nil_of_ne hne)
    exact hpout _ he (hqedges _ (heq ▸ he))
  obtain ⟨u, v, p', q', hpp, hqq, hcycle⟩ := hp.exists_isCycle_of_ne hq hpq
  have hp' : p'.IsPath := Walk.isPath_of_isSubwalk hpp hp
  have hq' : q'.IsPath := Walk.isPath_of_isSubwalk hqq hq
  have huv : u ≠ v := by
    intro heq
    subst v
    have hpn : p' = .nil := (Walk.isPath_iff_nil.mp hp').eq_nil
    have hqn : q' = .nil := (Walk.isPath_iff_nil.mp hq').eq_nil
    simpa [hpn, hqn] using hcycle
  have he := p'.mk_start_snd_mem_edges (Walk.not_nil_of_ne huv)
  have heout : s(u, p'.snd) ∉ C.edges := hpout _ (hpp.edges_subset he)
  have hecycle : s(u, p'.snd) ∈ (p'.append q'.reverse).edges := by
    simp only [Walk.edges_append, List.mem_append]
    exact Or.inl he
  have hediff : C.edges.toFinset ≠ (p'.append q'.reverse).edges.toFinset := by
    intro heq
    exact heout (List.mem_toFinset.mp (heq.symm ▸ List.mem_toFinset.mpr hecycle))
  have huC : u ∈ C.support := hqsupp _ (hqq.support_subset q'.start_mem_support)
  have hvC : v ∈ C.support := hqsupp _ (hqq.support_subset q'.end_mem_support)
  have huc : u ∈ (p'.append q'.reverse).support := (p'.append q'.reverse).start_mem_support
  have hvc : v ∈ (p'.append q'.reverse).support := by
    simp only [Walk.support_append, List.mem_append]
    exact Or.inl p'.end_mem_support
  have hcard := hG o u C (p'.append q'.reverse) hC hcycle hediff
  have hlarge : 1 < (C.support.toFinset ∩ (p'.append q'.reverse).support.toFinset).card := by
    apply Finset.one_lt_card.mpr
    exact ⟨u, by simpa using And.intro huC huc,
      v, by simpa using And.intro hvC hvc, huv⟩
  omega

private theorem walk_reaches_cycle {o x y : V} (C : G.Walk o o)
    (p : G.Walk x y) (hy : y ∈ C.support) :
    ∃ g, g ∈ C.support ∧ (G.deleteEdges C.edgeSet).Reachable x g := by
  induction p with
  | nil => exact ⟨_, hy, .rfl⟩
  | @cons x z y hxz p ih =>
    by_cases hx : x ∈ C.support
    · exact ⟨x, hx, .rfl⟩
    · obtain ⟨g, hg, hzg⟩ := ih hy
      refine ⟨g, hg, (show (G.deleteEdges C.edgeSet).Adj x z from ?_).reachable.trans hzg⟩
      refine deleteEdges_adj.mpr ⟨hxz, ?_⟩
      intro he
      exact hx (C.fst_mem_support_of_mem_edges he)

/-- Every vertex of a connected cactus reaches exactly one vertex of a fixed
simple cycle after all edges of that cycle have been deleted. -/
theorem cycle_gate (hG : G.Connected) (hcactus : IsCactus G) {o : V}
    (C : G.Walk o o) (hC : C.IsCycle) (x : V) :
    ∃! g, g ∈ C.support ∧ (G.deleteEdges C.edgeSet).Reachable x g := by
  obtain ⟨p⟩ := hG x o
  obtain ⟨g, hg, hxg⟩ := walk_reaches_cycle C p C.start_mem_support
  refine ⟨g, ⟨hg, hxg⟩, ?_⟩
  intro y hy
  exact cycle_vertices_separated hcactus C hC hy.1 hg (hy.2.symm.trans hxg)

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.cycle_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_gate

/-- If a cactus cycle visits every vertex, it already contains every edge. -/
theorem cycle_spanning_edges (hcactus : IsCactus G) {o : V}
    (C : G.Walk o o) (hC : C.IsCycle) (hspan : ∀ x, x ∈ C.support) :
    G.edgeSet = C.edgeSet := by
  ext e
  constructor
  · intro he
    by_contra hout
    obtain ⟨u,v⟩ := e
    have huv : G.Adj u v := he
    have hr : (G.deleteEdges C.edgeSet).Reachable u v :=
      (deleteEdges_adj.mpr ⟨huv,hout⟩).reachable
    have heq := cycle_vertices_separated hcactus C hC (hspan u) (hspan v) hr
    exact G.irrefl (heq ▸ huv)
  · intro he
    exact C.edges_subset_edgeSet he

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.cycle_spanning_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_spanning_edges

/-- The actual edges of G whose two endpoints lie on a specified side. -/
def sideGraph (G : SimpleGraph V) (A : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ A ∧ v ∈ A
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := by
    constructor
    intro u h
    exact G.irrefl h.1

private theorem side_support (A : Set V) {u v : V}
    (p : (sideGraph G A).Walk u v) (hu : u ∈ A) : ∀ z ∈ p.support, z ∈ A := by
  induction p with
  | nil =>
    intro z hz
    simp only [Walk.support_nil, List.mem_singleton] at hz
    subst z
    exact hu
  | @cons u w v h p ih =>
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · exact hz.symm ▸ hu
    · exact ih h.2.2 z hz

private def sideWalkToInduce (A : Set V) {u v : V}
    (p : (sideGraph G A).Walk u v) (hu : u ∈ A) (hv : v ∈ A) :
    (G.induce A).Walk ⟨u,hu⟩ ⟨v,hv⟩ :=
  (p.induce A (side_support A p hu)).mapLe (by intro a b h; exact h.1)

/-- A component off a cactus cycle and its complement form an actual
edge-disjoint one-vertex union at that component's unique cycle gate. -/
theorem cycle_component_decomposition (hG : G.Connected) (hcactus : IsCactus G)
    {o : V} (C : G.Walk o o) (hC : C.IsCycle) (x : V) :
    let R := G.deleteEdges C.edgeSet
    let A := {v | R.Reachable x v}
    ∃ g, g ∈ C.support ∧ g ∈ A ∧
      let B := Aᶜ ∪ {g}
      G = sideGraph G A ⊔ sideGraph G B ∧
      ThreeTerminalGluing.OneVertexUnion (sideGraph G A) (sideGraph G B) A B g ∧
      Disjoint (sideGraph G A).edgeSet (sideGraph G B).edgeSet ∧
      Disjoint (sideGraph G A).edgeSet C.edgeSet ∧
      (G.induce A).Connected ∧ (G.induce B).Connected := by
  classical
  dsimp only
  let R := G.deleteEdges C.edgeSet
  let A := {v | R.Reachable x v}
  obtain ⟨g, ⟨hgC, hxg⟩, huniq⟩ := cycle_gate hG hcactus C hC x
  let B := Aᶜ ∪ {g}
  have hgA : g ∈ A := hxg
  have hgB : g ∈ B := by simp [B]
  have hcross {u v : V} (huv : G.Adj u v) (hu : u ∈ A) (hv : v ∉ A) : u = g := by
    by_cases he : s(u,v) ∈ C.edges
    · exact huniq u ⟨C.fst_mem_support_of_mem_edges he, hu⟩
    · have huvr : R.Adj u v := deleteEdges_adj.mpr ⟨huv, he⟩
      exact (hv (hu.trans huvr.reachable)).elim
  have hinter {v : V} (hvA : v ∈ A) (hvB : v ∈ B) : v = g := by
    rcases hvB with hvB | hvB
    · exact (hvB hvA).elim
    · exact Set.mem_singleton_iff.mp hvB
  have hunion : G = sideGraph G A ⊔ sideGraph G B := by
    ext u v
    change G.Adj u v ↔
      (G.Adj u v ∧ u ∈ A ∧ v ∈ A) ∨ (G.Adj u v ∧ u ∈ B ∧ v ∈ B)
    constructor
    · intro huv
      by_cases hu : u ∈ A
      · by_cases hv : v ∈ A
        · exact Or.inl ⟨huv, hu, hv⟩
        · exact Or.inr ⟨huv, (hcross huv hu hv).symm ▸ hgB, Or.inl hv⟩
      · by_cases hv : v ∈ A
        · exact Or.inr ⟨huv, Or.inl hu, (hcross huv.symm hv hu).symm ▸ hgB⟩
        · exact Or.inr ⟨huv, Or.inl hu, Or.inl hv⟩
    · rintro (h | h) <;> exact h.1
  have hsplit : ThreeTerminalGluing.OneVertexUnion
      (sideGraph G A) (sideGraph G B) A B g :=
    ⟨fun {_ _} h => h.2, fun {_ _} h => h.2, fun {_} => hinter⟩
  refine ⟨g, hgC, hgA, hunion, hsplit, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro e heA heB
    obtain ⟨u, v⟩ := e
    have ha : G.Adj u v ∧ u ∈ A ∧ v ∈ A := heA
    have hb : G.Adj u v ∧ u ∈ B ∧ v ∈ B := heB
    have hu : u = g := hinter ha.2.1 hb.2.1
    have hv : v = g := hinter ha.2.2 hb.2.2
    exact G.irrefl (hu ▸ hv ▸ ha.1)
  · apply Set.disjoint_left.mpr
    intro e heA heC
    obtain ⟨u, v⟩ := e
    have ha : G.Adj u v ∧ u ∈ A ∧ v ∈ A := heA
    have hu : u = g := huniq u ⟨C.fst_mem_support_of_mem_edges heC, ha.2.1⟩
    have hv : v = g := huniq v ⟨C.snd_mem_support_of_mem_edges heC, ha.2.2⟩
    exact G.irrefl (hu ▸ hv ▸ ha.1)
  · letI : Nonempty A := ⟨⟨g,hgA⟩⟩
    constructor
    intro u v
    have hr : (sideGraph G A).Reachable u.1 v.1 := by
      apply (ThreeTerminalGluing.simultaneous_reachability hsplit
        (a := u.1) (b := v.1) (c := g) u.2 v.2 hgB).1.mp
      rw [← hunion]
      exact hG u.1 v.1
    obtain ⟨p⟩ := hr
    exact ⟨sideWalkToInduce A p u.2 v.2⟩
  · letI : Nonempty B := ⟨⟨g,hgB⟩⟩
    constructor
    intro u v
    have hswap : ThreeTerminalGluing.OneVertexUnion
        (sideGraph G B) (sideGraph G A) B A g :=
      ⟨hsplit.right_support, hsplit.left_support,
       fun {_} hvB hvA => hsplit.intersection hvA hvB⟩
    have hr : (sideGraph G B).Reachable u.1 v.1 := by
      apply (ThreeTerminalGluing.simultaneous_reachability hswap
        (a := u.1) (b := v.1) (c := g) u.2 v.2 hgA).1.mp
      rw [sup_comm, ← hunion]
      exact hG u.1 v.1
    obtain ⟨p⟩ := hr
    exact ⟨sideWalkToInduce B p u.2 v.2⟩

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.cycle_component_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_component_decomposition

private theorem cactus_induce (hcactus : IsCactus G) (A : Set V) :
    IsCactus (G.induce A) := by
  classical
  let f := (SimpleGraph.Embedding.induce (G := G) A).toHom
  have hf : Function.Injective f := Subtype.val_injective
  intro u v p q hp hq hne
  have hpe : (p.map f).edges.toFinset = p.edges.toFinset.image (Sym2.map f) := by
    ext e
    simp
  have hqe : (q.map f).edges.toFinset = q.edges.toFinset.image (Sym2.map f) := by
    ext e
    simp
  have hne' : (p.map f).edges.toFinset ≠ (q.map f).edges.toFinset := by
    intro he
    apply hne
    exact Finset.image_injective (Sym2.map.injective hf) (hpe.symm.trans (he.trans hqe))
  have h := hcactus (f u) (f v) (p.map f) (q.map f) (hp.map hf) (hq.map hf) hne'
  have hs : ((p.map f).support.toFinset ∩ (q.map f).support.toFinset) =
      (p.support.toFinset ∩ q.support.toFinset).image f := by
    rw [Finset.image_inter _ _ hf]
    congr 1 <;> ext z <;> simp
  rw [hs, Finset.card_image_of_injective _ hf] at h
  exact h

private theorem induce_card_lt_of_side_ssubset [Finite V] (A : Set V)
    (h : (sideGraph G A).edgeSet ⊂ G.edgeSet) :
    Nat.card (G.induce A).edgeSet < Nat.card G.edgeSet := by
  classical
  let f : G.induce A ↪g sideGraph G A :=
    { toFun := Subtype.val
      inj' := Subtype.val_injective
      map_rel_iff' := by intro u v; simp [sideGraph, u.property, v.property] }
  have hle := Nat.card_le_card_of_injective f.mapEdgeSet f.mapEdgeSet.injective
  exact hle.trans_lt (by simpa using Set.ncard_lt_ncard h)

/-- A vertex outside a cactus cycle gives two nonempty edge families and two
connected induced graphs, both with strictly fewer edges than the original. -/
theorem cycle_component_strict_edges [Finite V] (hG : G.Connected) (hcactus : IsCactus G)
    {o : V} (C : G.Walk o o) (hC : C.IsCycle) (x : V) (hx : x ∉ C.support) :
    let A := {v | (G.deleteEdges C.edgeSet).Reachable x v}
    ∃ g, g ∈ C.support ∧ g ∈ A ∧
      let B := Aᶜ ∪ {g}
      G = sideGraph G A ⊔ sideGraph G B ∧
      ThreeTerminalGluing.OneVertexUnion (sideGraph G A) (sideGraph G B) A B g ∧
      Disjoint (sideGraph G A).edgeSet (sideGraph G B).edgeSet ∧
      (G.induce A).Connected ∧ (G.induce B).Connected ∧
      IsCactus (G.induce A) ∧ IsCactus (G.induce B) ∧
      (sideGraph G A).edgeSet.Nonempty ∧ (sideGraph G B).edgeSet.Nonempty ∧
      (sideGraph G A).edgeSet ⊂ G.edgeSet ∧ (sideGraph G B).edgeSet ⊂ G.edgeSet ∧
      Nat.card (G.induce A).edgeSet < Nat.card G.edgeSet ∧
      Nat.card (G.induce B).edgeSet < Nat.card G.edgeSet := by
  classical
  dsimp only
  let A := {v | (G.deleteEdges C.edgeSet).Reachable x v}
  obtain ⟨g, hgC, hgA, hcover, hsplit, hdisj, hdisjC, hconnA, hconnB⟩ :=
    cycle_component_decomposition hG hcactus C hC x
  let B := Aᶜ ∪ {g}
  have hxA : x ∈ A := .rfl
  have hgB : g ∈ B := by simp [B]
  have hxg : x ≠ g := by intro he; subst g; exact hx hgC
  have hleft : (sideGraph G A).edgeSet.Nonempty := by
    have hr : (sideGraph G A).Reachable x g := by
      apply (ThreeTerminalGluing.simultaneous_reachability hsplit
        (a := x) (b := g) (c := g) hxA hgA hgB).1.mp
      rw [← hcover]
      exact hG x g
    obtain ⟨p⟩ := hr
    exact ⟨_, p.edges_subset_edgeSet (p.mk_start_snd_mem_edges (Walk.not_nil_of_ne hxg))⟩
  have hcycleRight : C.edgeSet ⊆ (sideGraph G B).edgeSet := by
    intro e heC
    have heG := C.edges_subset_edgeSet heC
    rw [hcover, edgeSet_sup] at heG
    rcases heG with heA | heB
    · exact (Set.disjoint_left.mp hdisjC heA heC).elim
    · exact heB
  have hright : (sideGraph G B).edgeSet.Nonempty :=
    ⟨_, hcycleRight (C.mk_start_snd_mem_edges hC.not_nil)⟩
  have hleA : (sideGraph G A).edgeSet ⊆ G.edgeSet := by
    rintro ⟨u,v⟩ h
    exact h.1
  have hleB : (sideGraph G B).edgeSet ⊆ G.edgeSet := by
    rintro ⟨u,v⟩ h
    exact h.1
  have hltA : (sideGraph G A).edgeSet ⊂ G.edgeSet := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hleA, ?_⟩
    intro heq
    obtain ⟨e, heB⟩ := hright
    exact Set.disjoint_left.mp hdisj (heq.symm ▸ hleB heB) heB
  have hltB : (sideGraph G B).edgeSet ⊂ G.edgeSet := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hleB, ?_⟩
    intro heq
    obtain ⟨e, heA⟩ := hleft
    exact Set.disjoint_left.mp hdisj heA (heq.symm ▸ hleA heA)
  exact ⟨g, hgC, hgA, hcover, hsplit, hdisj, hconnA, hconnB,
    cactus_induce hcactus A, cactus_induce hcactus B,
    hleft, hright, hltA, hltB,
    induce_card_lt_of_side_ssubset A hltA, induce_card_lt_of_side_ssubset B hltB⟩

/-- info: 'D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate.cycle_component_strict_edges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cycle_component_strict_edges

end D5.S3.StatisticalMechanics.Percolation.ThreeTerminalCactusGate
