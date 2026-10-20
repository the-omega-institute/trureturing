/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2HalfPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2HalfPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both literal half partitions retain the complete support and exact uncut edge inventory of the same supplied native cycle. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
import D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory
import D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open private half_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration

/-- The actual subtype cuts retain their literal raw three-cut side. -/
noncomputable def actualHalfCuts {m : ℕ} (D : Configuration m → Prop) (side : Bool) :
    Finset (Sym2 {x : Configuration m // D x}) := by
  classical
  exact Finset.univ.filter (fun e => HalfCut m side (Sym2.map Subtype.val e))

/-- The actual half-restored paths live in the same independent domain and
retain precisely the selected prior cycle's edges minus the selected three
cuts. `hD` is a domain identification, not a target partition certificate.
The end tables remain `halfStart/halfFinish` in their original native order. -/
theorem native_actual_j2_half_paths {m : ℕ} (hm : 5 ≤ m) (side : Bool)
    (D : Configuration m → Prop) (hD : ∀ x, D x ↔ F2Domain m x)
    {base : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base) (hw : w.IsHamiltonianCycle)
    (hinv : ∀ e, e ∈ w.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) :
    ∃ pieces : Fin 3 → Piece (domainGraph D),
      (∀ i, (pieces i).start.val = port m (halfStart side i) ∧
        (pieces i).finish.val = port m (halfFinish side i)) ∧
      (∀ i, (pieces i).walk.IsPath) ∧
      (∀ v : {x : Configuration m // D x}, ∃! i, v ∈ (pieces i).walk.support) ∧
      (∀ e, e ∈ (List.ofFn fun i =>
        (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten ↔
          e ∈ w.edges.map (Sym2.map Subtype.val) ∧ ¬ HalfCut m side e) ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.support).Perm w.support.tail ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.edges).Perm
        (w.edges.filter fun e => decide (e ∉ actualHalfCuts D side)) ∧
      (∀ e ∈ actualHalfCuts D side, e ∈ w.edges) := by
  classical
  obtain ⟨paths, hpath, hreach, _, hcover, hflat⟩ := native_j2_half_component_partition hm side
  let ambient := SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))
  let forget : domainGraph D →g ambient := ⟨Subtype.val, fun h => h⟩
  let raw := w.map forget
  have hrawEdges : raw.edges = w.edges.map (Sym2.map Subtype.val) :=
    SimpleGraph.Walk.edges_map forget w
  have hdomadj (x y : Configuration m) (hxy : (halfGraph m side).Adj x y) : D y := by
    have he : s(x, y) ∈ raw.edges := by
      rw [hrawEdges]
      exact (hinv _).mpr ((half_adj_iff m side x y).mp hxy).1.1
    have hy := raw.snd_mem_support_of_mem_edges he
    rw [show raw.support = w.support.map Subtype.val from SimpleGraph.Walk.support_map forget w] at hy
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
    exact hv ▸ v.property
  have hsub : halfGraph m side ≤ ambient := by
    intro x y hxy
    apply raw.adj_of_mem_edges
    rw [hrawEdges]
    exact (hinv _).mpr ((half_adj_iff m side x y).mp hxy).1.1
  have hpreserve (x y : Configuration m) (hx : D x)
      (hr : (halfGraph m side).Reachable x y) : D y := by
    obtain ⟨q⟩ := hr
    revert hx
    induction q with
    | nil => exact fun h => h
    | @cons a b c h q ih => exact fun _ => ih (hdomadj a b h)
  have hsD (i : Fin 3) (x : Configuration m) (hx : x ∈ (paths i).support) : D x :=
    hpreserve _ x ((hD _).mpr (native_j2_port_domain hm (halfStart side i)))
      ((hreach i x).mp hx)
  let lifted (i : Fin 3) := ((paths i).mapLe hsub).induce {x | D x} (by
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact hsD i x hx)
  let pieces (i : Fin 3) : Piece (domainGraph D) := ⟨_, _, lifted i⟩
  have hmap (i : Fin 3) : (pieces i).walk.map forget = (paths i).mapLe hsub := by
    exact SimpleGraph.Walk.map_induce _ _
  have hsmap (i : Fin 3) : (pieces i).walk.support.map Subtype.val = (paths i).support := by
    calc
      _ = ((pieces i).walk.map forget).support :=
        (SimpleGraph.Walk.support_map forget (pieces i).walk).symm
      _ = ((paths i).mapLe hsub).support := congrArg SimpleGraph.Walk.support (hmap i)
      _ = _ := SimpleGraph.Walk.support_mapLe_eq_support _ _
  have hemap (i : Fin 3) : (pieces i).walk.edges.map (Sym2.map Subtype.val) = (paths i).edges := by
    calc
      _ = ((pieces i).walk.map forget).edges :=
        (SimpleGraph.Walk.edges_map forget (pieces i).walk).symm
      _ = ((paths i).mapLe hsub).edges := congrArg SimpleGraph.Walk.edges (hmap i)
      _ = _ := SimpleGraph.Walk.edges_mapLe_eq_edges _ _
  have hsupport (i : Fin 3) (v : {x : Configuration m // D x}) :
      v ∈ (pieces i).walk.support ↔ v.val ∈ (paths i).support := by
    rw [← hsmap]
    constructor
    · intro hv
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    · intro hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      exact (Subtype.ext huv) ▸ hu
  have hpaths (i : Fin 3) : (pieces i).walk.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map (f := forget)
    rw [hmap]
    exact (hpath i).mapLe hsub
  have hcoverage (v : {x : Configuration m // D x}) :
      ∃! i, v ∈ (pieces i).walk.support := by
    obtain ⟨i, hi, huniq⟩ := (hcover v.val).mp ((hD v.val).mp v.property)
    exact ⟨i, (hsupport i v).mpr hi, fun j hj => huniq j ((hsupport j v).mp hj)⟩
  have hflatRaw (e : Sym2 (Configuration m)) :
      e ∈ (List.ofFn fun i =>
        (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten ↔
          e ∈ w.edges.map (Sym2.map Subtype.val) ∧ ¬ HalfCut m side e := by
    have heq : (List.ofFn fun i => (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten =
        (List.ofFn fun i => (paths i).edges).flatten := by
      congr 1
      exact congrArg List.ofFn (funext hemap)
    rw [heq, hflat, hinv]
    rfl
  have hflatMap : (((List.ofFn pieces).flatMap fun p => p.walk.edges).map
      (Sym2.map Subtype.val)) = (List.ofFn fun i =>
        (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten := by
    simp only [List.map_flatMap, List.flatMap, List.map_ofFn, Function.comp_def,
      List.map_flatten]
  have hmember (l : List (Sym2 {x : Configuration m // D x}))
      (e : Sym2 {x : Configuration m // D x}) :
      Sym2.map Subtype.val e ∈ l.map (Sym2.map Subtype.val) ↔ e ∈ l := by
    exact List.mem_map_of_injective (Sym2.map.injective Subtype.val_injective)
  have hedge (e : Sym2 {x : Configuration m // D x}) :
      e ∈ ((List.ofFn pieces).flatMap fun p => p.walk.edges) ↔
        e ∈ w.edges ∧ e ∉ actualHalfCuts D side := by
    rw [← hmember, hflatMap, hflatRaw, hmember]
    simp only [actualHalfCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨hs, he⟩ := actual_path_family_cycle_inventory pieces hpaths hcoverage w hw
    (actualHalfCuts D side) hedge
  refine ⟨pieces, fun _ => ⟨rfl, rfl⟩, hpaths, hcoverage, hflatRaw, hs, he, ?_⟩
  intro e hecut
  have hcut : HalfCut m side (Sym2.map Subtype.val e) := by
    simpa only [actualHalfCuts, Finset.mem_filter, Finset.mem_univ, true_and] using hecut
  obtain ⟨i, hi⟩ := hcut
  apply (hmember w.edges e).mp
  rw [hi]
  obtain ⟨_, _, _, hinv₀, _, hmarked⟩ := native_j2_hamiltonian_cycle_with_marked_edges hm
  exact (hinv _).mpr ((hinv₀ _).mp (hmarked (i, side)))

/-- Transport the paths of the same supplied raw cycle to an arbitrary
two-label frame. The original half table is mapped pointwise, preserving
the barred indices. The same actual mapped cycle appears in both support
and retained-edge conclusions, without choosing another witness. -/
theorem native_actual_j2_frame_half_paths {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (side : Bool)
    {rawBase : {v : Configuration m // F2Domain m v}}
    (rawWalk : (domainGraph (F2Domain m)).Walk rawBase rawBase)
    (hraw : rawWalk.IsHamiltonianCycle)
    (hinv : ∀ e, e ∈ rawWalk.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) :
    let iso := frameDomainIso hm F
    let w := rawWalk.map iso.toHom
    let cuts := (actualHalfCuts (F2Domain m) side).image (Sym2.map iso.toHom)
    ∃ pieces : Fin 3 → Piece (domainGraph (FrameDomain F)),
      (∀ i, (pieces i).start.val = relabel F * port m (halfStart side i) ∧
        (pieces i).finish.val = relabel F * port m (halfFinish side i)) ∧
      w.IsHamiltonianCycle ∧
      (∀ i, (pieces i).walk.IsPath) ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.support).Perm w.support.tail ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.edges).Perm
        (w.edges.filter fun e => decide (e ∉ cuts)) ∧
      (∀ e ∈ cuts, e ∈ w.edges) := by
  classical
  dsimp only
  let iso : domainGraph (F2Domain m) ≃g domainGraph (FrameDomain F) :=
    frameDomainIso hm F
  obtain ⟨rawPieces, hend, _, _, _, hs, he, hc⟩ :=
    native_actual_j2_half_paths hm side (F2Domain m) (fun _ => Iff.rfl) rawWalk hraw hinv
  let pieces (i : Fin 3) : Piece (domainGraph (FrameDomain F)) :=
    mapPiece iso.toHom (rawPieces i)
  have hlist : List.ofFn pieces = (List.ofFn rawPieces).map (mapPiece iso.toHom) := by
    rw [List.map_ofFn]
    rfl
  obtain ⟨_, hp, hs', he', hc'⟩ := actual_cycle_partition_map iso.toHom
    iso.toEquiv.injective rawWalk hraw.isCycle (List.ofFn rawPieces)
    (actualHalfCuts (F2Domain m) side) hs he hc
  refine ⟨pieces, ?_,
    SimpleGraph.Walk.IsHamiltonianCycle.map iso.toEquiv.bijective hraw,
    ?_, ?_, ?_, hc'⟩
  · intro i
    change relabel F * (rawPieces i).start.val = _ ∧
      relabel F * (rawPieces i).finish.val = _
    rw [(hend i).1, (hend i).2]
    exact ⟨rfl, rfl⟩
  · intro i
    apply hp (pieces i)
    rw [← hlist]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · rw [hlist]
    exact hs'
  · rw [hlist]
    exact he'

#print axioms native_actual_j2_half_paths
#print axioms native_actual_j2_frame_half_paths

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
