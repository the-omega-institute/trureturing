/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SixthComponent
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SixthComponent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual six-cut paths and five whole words identify the sixth J2 component. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
import D5.S3.Combinatorics.Graph.Walks.EdgeSlicingCutEndpoints
import Mathlib.Data.List.Nodup

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SixthComponent

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open Equiv Fin.NatCast
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent


open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
open private surviving_adj_iff markedCut_injective actual_port_leaf from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel
open private j2_native_survives j2_a_not_marked from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingRows

private theorem actual_six_cut_slicing_with_endpoints {m : ℕ} (hm : 5 ≤ m) :
    ∃ pieces : List (D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece
        (domainGraph (F2Domain m))),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      (∀ v : {x : Configuration m // F2Domain m x},
        (pieces.flatMap fun z => z.walk.support).count v = 1) ∧
      (∀ e : Sym2 (Configuration m),
        e ∈ (pieces.flatMap fun z => z.walk.edges).map (Sym2.map Subtype.val) ↔
          SurvivingEdge m e) ∧
      pieces.length = 6 ∧
      ∀ z ∈ pieces,
        (∃ q : Fin 3 × Bool × Bool, z.start.val = port m q) ∧
        (∃ q : Fin 3 × Bool × Bool, z.finish.val = port m q) := by
  classical
  obtain ⟨base, w, hw, hinv, hports, hmarked⟩ :=
    native_j2_hamiltonian_cycle_with_marked_edges hm
  let cut : Fin 3 × Bool → Sym2 {x : Configuration m // F2Domain m x} := fun q =>
    s(⟨port m (q.1, q.2, false), hports (q.1, q.2, false)⟩,
      ⟨port m (q.1, q.2, true), hports (q.1, q.2, true)⟩)
  have hmap (q : Fin 3 × Bool) : Sym2.map Subtype.val (cut q) = markedEdge m q := rfl
  have hmapinj : Function.Injective
      (Sym2.map (Subtype.val : {x : Configuration m // F2Domain m x} → Configuration m)) :=
    Sym2.map.injective Subtype.val_injective
  have hcutinj : Function.Injective cut := by
    intro p q he
    apply markedCut_injective hm
    simpa only [hmap] using congrArg (Sym2.map Subtype.val) he
  let E : Finset (Sym2 {x : Configuration m // F2Domain m x}) := Finset.univ.image cut
  have hE : E.Nonempty := by
    exact ⟨cut (0, false), Finset.mem_image.mpr ⟨(0, false), Finset.mem_univ _, rfl⟩⟩
  have hE_marked (e : Sym2 {x : Configuration m // F2Domain m x}) :
      e ∈ E ↔ MarkedCut m (Sym2.map Subtype.val e) := by
    constructor
    · intro he
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
      exact ⟨q, hmap q⟩
    · rintro ⟨q, hq⟩
      have he : e = cut q := hmapinj (hq.trans (hmap q).symm)
      rw [he]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
  have hcuts : ∀ e ∈ E, e ∈ w.edgeSet := by
    intro e he
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
    have hq : Sym2.map Subtype.val (cut q) ∈ w.edges.map (Sym2.map Subtype.val) := by
      rw [hmap]
      exact hmarked q
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hq
    have heq' : e = cut q := hmapinj heq
    simpa only [← heq', SimpleGraph.Walk.mem_edgeSet] using he
  obtain ⟨pieces, hpath, hsupport, hedges, hlength, hendpoints⟩ :=
    D5.S3.Combinatorics.Graph.Walks.EdgeSlicingCutEndpoints.exists_cycle_edge_slicing_with_cut_endpoints
      E w hw hE hcuts
  refine ⟨pieces, hpath, ?_, ?_, ?_, ?_⟩
  · intro v
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using hsupport v
  · intro e
    constructor
    · intro he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      obtain ⟨hfw, hfE⟩ := (hedges f).mp hf
      have hn : (F2NativeEdge m (Sym2.map Subtype.val f) ∧
          ¬ F2DeletedEdge m (Sym2.map Subtype.val f)) ∨
          F2Seam m (Sym2.map Subtype.val f) :=
        (hinv _).mp (List.mem_map.mpr ⟨f, hfw, rfl⟩)
      exact ⟨hn, fun hmark => hfE ((hE_marked f).mpr hmark)⟩
    · rintro ⟨hn, hmark⟩
      obtain ⟨f, hfw, hfe⟩ := List.mem_map.mp ((hinv e).mpr hn)
      refine List.mem_map.mpr ⟨f, (hedges f).mpr ⟨hfw, ?_⟩, hfe⟩
      intro hfE
      apply hmark
      rw [← hfe]
      exact (hE_marked f).mp hfE
  · rw [hlength]
    simp only [E, Finset.card_image_of_injective _ hcutinj, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]

  · have hport (v : {x : Configuration m // F2Domain m x})
        (hv : ∃ e ∈ E, v ∈ e) : ∃ q : Fin 3 × Bool × Bool, v.val = port m q := by
      obtain ⟨e, he, hve⟩ := hv
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
      change v ∈ s(⟨port m (q.1, q.2, false), hports (q.1, q.2, false)⟩,
        ⟨port m (q.1, q.2, true), hports (q.1, q.2, true)⟩) at hve
      rcases Sym2.mem_iff.mp hve with hv | hv
      · exact ⟨(q.1, q.2, false), congrArg Subtype.val hv⟩
      · exact ⟨(q.1, q.2, true), congrArg Subtype.val hv⟩
    intro z hz
    exact ⟨hport z.start (hendpoints z hz).1, hport z.finish (hendpoints z hz).2⟩


private theorem actual_surviving_path_partition {m : ℕ} (hm : 5 ≤ m) :
    ∃ pieces : List (D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece
        (survivingGraph m)),
      (∀ z ∈ pieces, z.walk.IsPath) ∧
      (pieces.flatMap fun z => z.walk.support).Nodup ∧
      (∀ x, x ∈ (pieces.flatMap fun z => z.walk.support) ↔ F2Domain m x) ∧
      (∀ e, e ∈ (pieces.flatMap fun z => z.walk.edges) ↔ SurvivingEdge m e) ∧
      pieces.length = 6 ∧
      ∀ z ∈ pieces,
        (∃ q : Fin 3 × Bool × Bool, z.start = port m q) ∧
        (∃ q : Fin 3 × Bool × Bool, z.finish = port m q) := by
  classical
  obtain ⟨pieces, hpath, hcount, hinventory, hlength, hendpoints⟩ :=
    actual_six_cut_slicing_with_endpoints hm
  let f : domainGraph (F2Domain m) →g
      SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m)) :=
    ⟨Subtype.val, fun h => h⟩
  have hf : (f : {x : Configuration m // F2Domain m x} → Configuration m) =
      Subtype.val := rfl
  have htransfer (z : {z // z ∈ pieces}) :
      ∀ e, e ∈ (z.val.walk.map f).edges → e ∈ (survivingGraph m).edgeSet := by
    intro e he
    have hmem : e ∈ (pieces.flatMap fun z => z.walk.edges).map
        (Sym2.map Subtype.val) := by
      rw [SimpleGraph.Walk.edges_map] at he
      obtain ⟨rawEdge, hraw, rfl⟩ := List.mem_map.mp he
      exact List.mem_map.mpr
        ⟨rawEdge, List.mem_flatMap.mpr ⟨z.val, z.property, hraw⟩, rfl⟩
    have hs := (hinventory e).mp hmem
    obtain ⟨⟨x, y⟩, rfl⟩ := Sym2.mk_surjective e
    change (survivingGraph m).Adj x y
    exact (surviving_adj_iff m x y).mpr
      ⟨hs, ((z.val.walk.map f).adj_of_mem_edges he).ne⟩
  let lift : {z // z ∈ pieces} →
      D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece (survivingGraph m) := fun z =>
    ⟨z.val.start.val, z.val.finish.val,
      (z.val.walk.map f).transfer (survivingGraph m) (htransfer z)⟩
  let lifted := pieces.attach.map lift
  have hs : (lifted.flatMap fun z => z.walk.support) =
      (pieces.flatMap fun z => z.walk.support).map Subtype.val := by
    calc
      _ = pieces.attach.flatMap (fun z => z.val.walk.support.map Subtype.val) := by
        simp only [lifted, List.flatMap_map, lift, SimpleGraph.Walk.support_transfer,
          SimpleGraph.Walk.support_map, hf]
      _ = (pieces.attach.flatMap fun z => z.val.walk.support).map Subtype.val := by
        rw [List.map_flatMap]
      _ = _ := by
        rw [← List.flatMap_map Subtype.val (fun z => z.walk.support) pieces.attach,
          List.attach_map_subtype_val]
  have he : (lifted.flatMap fun z => z.walk.edges) =
      (pieces.flatMap fun z => z.walk.edges).map (Sym2.map Subtype.val) := by
    calc
      _ = pieces.attach.flatMap (fun z => z.val.walk.edges.map (Sym2.map Subtype.val)) := by
        simp only [lifted, List.flatMap_map, lift, SimpleGraph.Walk.edges_transfer,
          SimpleGraph.Walk.edges_map, hf]
      _ = (pieces.attach.flatMap fun z => z.val.walk.edges).map (Sym2.map Subtype.val) := by
        rw [List.map_flatMap]
      _ = _ := by
        rw [← List.flatMap_map Subtype.val (fun z => z.walk.edges) pieces.attach,
          List.attach_map_subtype_val]
  have hn : (pieces.flatMap fun z => z.walk.support).Nodup :=
    List.nodup_iff_count_le_one.mpr (fun x => by rw [hcount x])
  refine ⟨lifted, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hz
    apply SimpleGraph.Walk.IsPath.mk'
    simpa only [lift, SimpleGraph.Walk.support_transfer, SimpleGraph.Walk.support_map, hf] using
      (hpath z.val z.property).support_nodup.map Subtype.val_injective
  · rw [hs]
    exact hn.map Subtype.val_injective
  · intro x
    rw [hs]
    constructor
    · intro hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.property
    · intro hx
      let v : {x : Configuration m // F2Domain m x} := ⟨x, hx⟩
      have hv : v ∈ (pieces.flatMap fun z => z.walk.support) := by
        exact List.count_pos_iff.mp (by rw [hcount v]; omega)
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
  · intro e
    rw [he]
    exact hinventory e
  · simpa only [lifted, List.length_map, List.length_attach] using hlength
  · intro z hz
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hz
    exact hendpoints z.val z.property

#print axioms actual_surviving_path_partition


private theorem partition_piece_full_component {V : Type*} [DecidableEq V]
    {G : SimpleGraph V}
    (pieces : List (D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece G))
    (hn : (pieces.flatMap fun z => z.walk.support).Nodup)
    (hedges : ∀ x y, G.Adj x y → s(x, y) ∈ (pieces.flatMap fun z => z.walk.edges))
    (p : D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece G) (hp : p ∈ pieces) :
    (∀ x, x ∈ p.walk.support ↔ G.Reachable p.start x) ∧
      ∀ x y, G.Adj x y ∧ G.Reachable p.start x ↔ s(x, y) ∈ p.walk.edges := by
  letI : Std.Symm (fun p q : D5.S3.Combinatorics.Graph.Walks.EdgeSlicing.Piece G =>
      List.Disjoint p.walk.support q.walk.support) := ⟨fun _ _ h => h.symm⟩
  have hd := (List.nodup_flatMap.mp hn).2
  have hsaturated : ∀ x y, x ∈ p.walk.support → G.Adj x y → p.walk.toSubgraph.Adj x y := by
    intro x y hx hxy
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.mp (hedges x y hxy)
    have hqx := q.walk.fst_mem_support_of_mem_edges he
    have hqp : q = p := by
      by_contra hne
      exact List.disjoint_left.mp (hd.forall hq hp hne) hqx hx
    subst q
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
  have hvertices : ∀ x, x ∈ p.walk.support ↔ G.Reachable p.start x := by
    intro x
    constructor
    · intro hx
      exact (p.walk.takeUntil x hx).reachable
    · intro hx
      exact p.walk.mem_verts_toSubgraph.mp
        (hx.mem_subgraphVerts (H := p.walk.toSubgraph)
          (fun y hy z hyz => hsaturated y z (p.walk.mem_verts_toSubgraph.mp hy) hyz)
          p.walk.start_mem_verts_toSubgraph)
  refine ⟨hvertices, ?_⟩
  intro x y
  constructor
  · rintro ⟨hxy, hx⟩
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp
      (hsaturated x y ((hvertices x).mpr hx) hxy)
  · intro he
    have hs := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
    exact ⟨hs.adj_sub, (hvertices x).mp
      (SimpleGraph.Walk.mem_support_of_adj_toSubgraph hs)⟩

/-- A graph leaf cannot occur strictly inside an actual simple path. -/
private theorem leaf_in_path_is_endpoint {V : Type*} [DecidableEq V] [Finite V]
    {G : SimpleGraph V} {a b x : V} (p : G.Walk a b) (hp : p.IsPath)
    (hx : x ∈ p.support) (hleaf : (G.neighborSet x).Subsingleton) :
    x = a ∨ x = b := by
  obtain ⟨i, hi, hib⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
  by_cases hi0 : i = 0
  · left
    simpa only [hi0, SimpleGraph.Walk.getVert_zero] using hi.symm
  · by_cases hil : i = p.length
    · right
      simpa only [hil, SimpleGraph.Walk.getVert_length] using hi.symm
    · have hilt : i < p.length := by omega
      have htwo := hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
      have hs : p.toSubgraph.neighborSet (p.getVert i) ⊆ G.neighborSet (p.getVert i) :=
        fun _ h => h.adj_sub
      have hle := Set.ncard_le_ncard hs
      have hone : (G.neighborSet (p.getVert i)).ncard ≤ 1 := by
        rw [hi]
        exact Set.ncard_le_one_iff_subsingleton.mpr hleaf
      omega

#print axioms partition_piece_full_component
#print axioms leaf_in_path_is_endpoint


private theorem actual_port_a_neighbor {m : ℕ} (hm : 5 ≤ m)
    (q : Fin 3 × Bool × Bool) :
    (survivingGraph m).Adj (port m q) (port m q * a m) := by
  apply j2_native_survives hm (port m q) (a m)
    (native_j2_port_domain hm q) (Or.inl rfl) _ (j2_a_not_marked hm _)
  intro hd
  have hl := native_j2_port_last hm q
  rcases (native_f2_a_cut_classification (by omega : 4 ≤ m) (port m q)).mp hd with he | he
  · have hx : port m q ∈ s(1, a m) := he ▸ Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hx with hx | hx
    all_goals
      rw [hx] at hl
      simp (disch := omega) [Equiv.Perm.one_apply, a_apply] at hl
      omega
  · have hx : port m q ∈
        s(Equiv.swap (0 : Fin (m + 1)) (Fin.last m),
          Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * a m) :=
      he ▸ Sym2.mem_mk_left _ _
    rcases Sym2.mem_iff.mp hx with hx | hx
    all_goals
      rw [hx] at hl
      simp (disch := omega) [Equiv.Perm.mul_apply, a_apply,
        Equiv.swap_apply_def, Fin.ext_iff] at hl
      omega

/-- The sixth actual component runs from L₁ to bar L₀. Its actual path and
full component inventory are obtained from the genuine six-cut slicing. -/
private theorem actual_sixth_full_component {m : ℕ} (hm : 5 ≤ m) :
    ∃ w : (survivingGraph m).Walk (port m (1, false, true)) (port m (0, true, true)),
      w.IsPath ∧
      (∀ x, x ∈ w.support ↔ (survivingGraph m).Reachable (port m (1, false, true)) x) ∧
      ∀ x y, (survivingGraph m).Adj x y ∧
        (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ w.edges := by
  classical
  let first : Fin 5 → Fin 3 × Bool × Bool := fun i =>
    match i.val with
    | 0 => (0, false, false)
    | 1 => (0, false, true)
    | 2 => (1, false, false)
    | 3 => (2, false, true)
    | _ => (0, true, false)
  let last : Fin 5 → Fin 3 × Bool × Bool := fun i =>
    match i.val with
    | 0 => (2, false, false)
    | 1 => (1, true, true)
    | 2 => (2, true, true)
    | 3 => (2, true, false)
    | _ => (1, true, false)
  have hfirst (i : Fin 5) : wordStart m i = port m (first i) := by
    fin_cases i <;> rfl
  have hlast (i : Fin 5) : wordFinish m i = port m (last i) := by
    fin_cases i <;> rfl
  have hfirst_ne (i : Fin 5) : (1, false, true) ≠ first i := by
    fin_cases i <;> decide
  have hlast_ne (i : Fin 5) : (1, false, true) ≠ last i := by
    fin_cases i <;> decide
  have hremaining : ∀ q : Fin 3 × Bool × Bool,
      q = (1, false, true) ∨ q = (0, true, true) ∨
        ∃ i : Fin 5, q = first i ∨ q = last i := by
    decide
  have hnotfirst (i : Fin 5) :
      ¬ (survivingGraph m).Reachable (port m (1, false, true)) (wordStart m i) := by
    intro hr
    obtain ⟨w, hp, _, _, hvertices, _⟩ := native_j2_word_full_component hm i
    have ha := (hvertices (port m (1, false, true))).mpr hr.symm
    rcases leaf_in_path_is_endpoint w hp ha (actual_port_leaf hm (1, false, true)) with he | he
    · exact hfirst_ne i (native_j2_port_injective hm (he.trans (hfirst i)))
    · exact hlast_ne i (native_j2_port_injective hm (he.trans (hlast i)))
  have hnotlast (i : Fin 5) :
      ¬ (survivingGraph m).Reachable (port m (1, false, true)) (wordFinish m i) := by
    intro hr
    obtain ⟨w, _, _, _, _, _⟩ := native_j2_word_full_component hm i
    exact hnotfirst i (hr.trans w.reachable.symm)
  obtain ⟨pieces, hpaths, hn, hdomain, hinventory, _, hendpoints⟩ :=
    actual_surviving_path_partition hm
  have ha : port m (1, false, true) ∈ (pieces.flatMap fun z => z.walk.support) :=
    (hdomain _).mpr (native_j2_port_domain hm (1, false, true))
  obtain ⟨p, hp, hap⟩ := List.mem_flatMap.mp ha
  have hall : ∀ x y, (survivingGraph m).Adj x y →
      s(x, y) ∈ (pieces.flatMap fun z => z.walk.edges) := by
    intro x y hxy
    exact (hinventory _).mpr ((surviving_adj_iff m x y).mp hxy).1
  obtain ⟨hvertices, hedges⟩ := partition_piece_full_component pieces hn hall p hp
  have haroot := (hvertices _).mp hap
  have hroots (x : Configuration m) :
      (survivingGraph m).Reachable p.start x ↔
        (survivingGraph m).Reachable (port m (1, false, true)) x :=
    ⟨fun h => haroot.symm.trans h, fun h => haroot.trans h⟩
  have hne : p.start ≠ p.finish := by
    intro heq
    have hnil := (hpaths p hp).nil_iff_eq.mpr heq
    have hedge := (hedges _ _).mp ⟨actual_port_a_neighbor hm (1, false, true), haroot⟩
    rw [SimpleGraph.Walk.edges_eq_nil.mpr hnil] at hedge
    exact List.not_mem_nil hedge
  have hother (v : Configuration m)
      (hv : ∃ q : Fin 3 × Bool × Bool, v = port m q)
      (hr : (survivingGraph m).Reachable (port m (1, false, true)) v)
      (hne : v ≠ port m (1, false, true)) : v = port m (0, true, true) := by
    obtain ⟨q, rfl⟩ := hv
    rcases hremaining q with hq | hq | ⟨i, hq | hq⟩
    · exact (hne (congrArg (port m) hq)).elim
    · exact congrArg (port m) hq
    · exact (hnotfirst i (by simpa only [hq, ← hfirst i] using hr)).elim
    · exact (hnotlast i (by simpa only [hq, ← hlast i] using hr)).elim
  rcases leaf_in_path_is_endpoint p.walk (hpaths p hp) hap
      (actual_port_leaf hm (1, false, true)) with has | haf
  · have hfinish : p.finish = port m (0, true, true) :=
      hother p.finish (hendpoints p hp).2
        (haroot.symm.trans p.walk.reachable) (fun h => hne (has.symm.trans h.symm))
    refine ⟨p.walk.copy has.symm hfinish, ?_, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.isPath_copy] using hpaths p hp
    · intro x
      simpa only [SimpleGraph.Walk.support_copy] using (hvertices x).trans (hroots x)
    · intro x y
      simpa only [SimpleGraph.Walk.edges_copy] using
        (show (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ p.walk.edges by
          rw [← hroots x]; exact hedges x y)
  · have hstart : p.start = port m (0, true, true) :=
      hother p.start (hendpoints p hp).1 haroot.symm
        (fun h => hne (h.trans haf))
    refine ⟨p.walk.reverse.copy haf.symm hstart, ?_, ?_, ?_⟩
    · simpa only [SimpleGraph.Walk.isPath_copy] using (hpaths p hp).reverse
    · intro x
      simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse,
        List.mem_reverse] using (hvertices x).trans (hroots x)
    · intro x y
      simpa only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_reverse,
        List.mem_reverse] using
        (show (survivingGraph m).Adj x y ∧
          (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ p.walk.edges by
          rw [← hroots x]; exact hedges x y)

#print axioms actual_port_a_neighbor
#print axioms actual_sixth_full_component


/-- The remaining two actual marked ports are joined by the sixth complete
path component of the same actual surviving F2 graph. -/
theorem native_j2_sixth_full_component {m : ℕ} (hm : 5 ≤ m) :
    ∃ w : (survivingGraph m).Walk (port m (1, false, true)) (port m (0, true, true)),
      w.IsPath ∧
      (∀ x, x ∈ w.support ↔ (survivingGraph m).Reachable (port m (1, false, true)) x) ∧
      ∀ x y, (survivingGraph m).Adj x y ∧
        (survivingGraph m).Reachable (port m (1, false, true)) x ↔ s(x, y) ∈ w.edges :=
  actual_sixth_full_component hm

#print axioms native_j2_sixth_full_component

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SixthComponent
