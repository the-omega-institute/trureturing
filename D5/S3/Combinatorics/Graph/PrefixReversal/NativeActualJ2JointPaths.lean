/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The six literal joint components retain the complete support and exact uncut edge inventory of the same supplied native cycle. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
import D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory
import D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2JointPaths

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPathFamilyInventory
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
open private surviving_adj_iff from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel

/-- All six independently specified raw marked cuts in the supplied domain. -/
noncomputable def actualJointCuts {m : ℕ} (D : Configuration m → Prop) :
    Finset (Sym2 {x : Configuration m // D x}) := by
  classical
  exact Finset.univ.filter (fun e => MarkedCut m (Sym2.map Subtype.val e))

/-- The six paths partition the same supplied cycle support and retain
exactly its uncut edges. Only independent native domain and inventory
identification are required; no target joint partition is assumed. -/
theorem native_actual_j2_joint_paths {m : ℕ} (hm : 5 ≤ m)
    (D : Configuration m → Prop) (hD : ∀ x, D x ↔ F2Domain m x)
    {base : {x : Configuration m // D x}}
    (w : (domainGraph D).Walk base base) (hw : w.IsHamiltonianCycle)
    (hinv : ∀ e, e ∈ w.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) :
    ∃ pieces : Fin 6 → Piece (domainGraph D),
      (∀ i, (pieces i).start.val = port m (componentStartPort i) ∧
        (pieces i).finish.val = port m (componentFinishPort i)) ∧
      (∀ i, (pieces i).walk.IsPath) ∧
      (∀ v : {x : Configuration m // D x}, ∃! i, v ∈ (pieces i).walk.support) ∧
      (∀ e, e ∈ (List.ofFn fun i =>
        (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten ↔
          e ∈ w.edges.map (Sym2.map Subtype.val) ∧ ¬ MarkedCut m e) ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.support).Perm w.support.tail ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.edges).Perm
        (w.edges.filter fun e => decide (e ∉ actualJointCuts D)) ∧
      (∀ e ∈ actualJointCuts D, e ∈ w.edges) := by
  classical
  obtain ⟨paths, hpath, hreach, hedgePaths, hcover⟩ := native_j2_six_component_partition hm
  let ambient := SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))
  let forget : domainGraph D →g ambient := ⟨Subtype.val, fun h => h⟩
  let raw := w.map forget
  have hrawEdges : raw.edges = w.edges.map (Sym2.map Subtype.val) :=
    SimpleGraph.Walk.edges_map forget w
  have hdomadj (x y : Configuration m) (hxy : (survivingGraph m).Adj x y) : D y := by
    have he : s(x, y) ∈ raw.edges := by
      rw [hrawEdges]
      exact (hinv _).mpr ((surviving_adj_iff m x y).mp hxy).1.1
    have hy := raw.snd_mem_support_of_mem_edges he
    rw [show raw.support = w.support.map Subtype.val from SimpleGraph.Walk.support_map forget w] at hy
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hy
    exact hv ▸ v.property
  have hsub : survivingGraph m ≤ ambient := by
    intro x y hxy
    apply raw.adj_of_mem_edges
    rw [hrawEdges]
    exact (hinv _).mpr ((surviving_adj_iff m x y).mp hxy).1.1
  have hpreserve (x y : Configuration m) (hx : D x)
      (hr : (survivingGraph m).Reachable x y) : D y := by
    obtain ⟨q⟩ := hr
    revert hx
    induction q with
    | nil => exact fun h => h
    | @cons a b c h q ih => exact fun _ => ih (hdomadj a b h)
  have hsD (i : Fin 6) (x : Configuration m) (hx : x ∈ (paths i).support) : D x :=
    hpreserve _ x ((hD _).mpr (native_j2_port_domain hm (componentStartPort i)))
      ((hreach i x).mp hx)
  let lifted (i : Fin 6) := ((paths i).mapLe hsub).induce {x | D x} (by
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact hsD i x hx)
  let pieces (i : Fin 6) : Piece (domainGraph D) := ⟨_, _, lifted i⟩
  have hmap (i : Fin 6) : (pieces i).walk.map forget = (paths i).mapLe hsub := by
    exact SimpleGraph.Walk.map_induce _ _
  have hsmap (i : Fin 6) : (pieces i).walk.support.map Subtype.val = (paths i).support := by
    calc
      _ = ((pieces i).walk.map forget).support :=
        (SimpleGraph.Walk.support_map forget (pieces i).walk).symm
      _ = ((paths i).mapLe hsub).support := congrArg SimpleGraph.Walk.support (hmap i)
      _ = _ := SimpleGraph.Walk.support_mapLe_eq_support _ _
  have hemap (i : Fin 6) : (pieces i).walk.edges.map (Sym2.map Subtype.val) = (paths i).edges := by
    calc
      _ = ((pieces i).walk.map forget).edges :=
        (SimpleGraph.Walk.edges_map forget (pieces i).walk).symm
      _ = ((paths i).mapLe hsub).edges := congrArg SimpleGraph.Walk.edges (hmap i)
      _ = _ := SimpleGraph.Walk.edges_mapLe_eq_edges _ _
  have hsupport (i : Fin 6) (v : {x : Configuration m // D x}) :
      v ∈ (pieces i).walk.support ↔ v.val ∈ (paths i).support := by
    rw [← hsmap]
    constructor
    · intro hv
      exact List.mem_map.mpr ⟨v, hv, rfl⟩
    · intro hv
      obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
      exact (Subtype.ext huv) ▸ hu
  have hpaths (i : Fin 6) : (pieces i).walk.IsPath := by
    apply SimpleGraph.Walk.IsPath.of_map (f := forget)
    rw [hmap]
    exact (hpath i).mapLe hsub
  have hcoverage (v : {x : Configuration m // D x}) :
      ∃! i, v ∈ (pieces i).walk.support := by
    obtain ⟨i, hi, huniq⟩ := (hcover v.val).mp ((hD v.val).mp v.property)
    exact ⟨i, (hsupport i v).mpr hi, fun j hj => huniq j ((hsupport j v).mp hj)⟩
  have hflat (e : Sym2 (Configuration m)) :
      e ∈ (List.ofFn fun i => (paths i).edges).flatten ↔ SurvivingEdge m e := by
    induction e using Sym2.inductionOn with
    | _ x y =>
      constructor
      · intro he
        obtain ⟨es, hes, he⟩ := List.mem_flatten.mp he
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hes
        exact ((surviving_adj_iff m x y).mp ((paths i).adj_of_mem_edges he)).1
      · intro he
        have hemem : s(x, y) ∈ raw.edges := by
          rw [hrawEdges]
          exact (hinv _).mpr he.1
        have hxy : (survivingGraph m).Adj x y :=
          (surviving_adj_iff m x y).mpr ⟨he, (raw.adj_of_mem_edges hemem).ne⟩
        have hxD : D x := hdomadj y x hxy.symm
        obtain ⟨i, hi, _⟩ := (hcover x).mp ((hD x).mp hxD)
        exact List.mem_flatten.mpr ⟨(paths i).edges,
          List.mem_ofFn.mpr ⟨i, rfl⟩,
          (hedgePaths i x y).mp ⟨hxy, (hreach i x).mp hi⟩⟩
  have hflatRaw (e : Sym2 (Configuration m)) :
      e ∈ (List.ofFn fun i =>
        (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten ↔
          e ∈ w.edges.map (Sym2.map Subtype.val) ∧ ¬ MarkedCut m e := by
    have heq : (List.ofFn fun i => (pieces i).walk.edges.map (Sym2.map Subtype.val)).flatten =
        (List.ofFn fun i => (paths i).edges).flatten := by
      congr 1
      exact congrArg List.ofFn (funext hemap)
    rw [heq, hflat]
    change ((F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) ∧
      ¬ MarkedCut m e ↔ _
    rw [hinv]
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
        e ∈ w.edges ∧ e ∉ actualJointCuts D := by
    rw [← hmember, hflatMap, hflatRaw, hmember]
    simp only [actualJointCuts, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨hs, he⟩ := actual_path_family_cycle_inventory pieces hpaths hcoverage w hw
    (actualJointCuts D) hedge
  refine ⟨pieces, fun _ => ⟨rfl, rfl⟩, hpaths, hcoverage, hflatRaw, hs, he, ?_⟩
  intro e hecut
  have hcut : MarkedCut m (Sym2.map Subtype.val e) := by
    simpa only [actualJointCuts, Finset.mem_filter, Finset.mem_univ, true_and] using hecut
  obtain ⟨i, hi⟩ := hcut
  apply (hmember w.edges e).mp
  rw [hi]
  obtain ⟨_, _, _, hinv₀, _, hmarked⟩ := native_j2_hamiltonian_cycle_with_marked_edges hm
  exact (hinv _).mpr ((hinv₀ _).mp (hmarked i))

/-- Transport the paths of the same supplied raw cycle to an arbitrary
two-label frame. The original six-component table is mapped pointwise, preserving
the barred indices. The same actual mapped cycle appears in both support
and retained-edge conclusions, without choosing another witness. -/
theorem native_actual_j2_frame_joint_paths {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2)
    {rawBase : {v : Configuration m // F2Domain m v}}
    (rawWalk : (domainGraph (F2Domain m)).Walk rawBase rawBase)
    (hraw : rawWalk.IsHamiltonianCycle)
    (hinv : ∀ e, e ∈ rawWalk.edges.map (Sym2.map Subtype.val) ↔
      (F2NativeEdge m e ∧ ¬ F2DeletedEdge m e) ∨ F2Seam m e) :
    let iso : domainGraph (F2Domain m) ≃g domainGraph (FrameDomain F) := frameDomainIso hm F
    let w := rawWalk.map iso.toHom
    let cuts := (actualJointCuts (F2Domain m)).image (Sym2.map iso.toHom)
    ∃ pieces : Fin 6 → Piece (domainGraph (FrameDomain F)),
      (∀ i, (pieces i).start.val = relabel F * port m (componentStartPort i) ∧
        (pieces i).finish.val = relabel F * port m (componentFinishPort i)) ∧
      w.IsHamiltonianCycle ∧
      (∀ i, (pieces i).walk.IsPath) ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.support).Perm w.support.tail ∧
      ((List.ofFn pieces).flatMap fun p => p.walk.edges).Perm
        (w.edges.filter fun e => decide (e ∉ cuts)) ∧
      (∀ e ∈ cuts, e ∈ w.edges) := by
  classical
  dsimp only
  let iso : domainGraph (F2Domain m) ≃g domainGraph (FrameDomain F) := frameDomainIso hm F
  obtain ⟨rawPieces, hend, _, _, _, hs, he, hc⟩ :=
    native_actual_j2_joint_paths hm (F2Domain m) (fun _ => Iff.rfl) rawWalk hraw hinv
  let pieces (i : Fin 6) : Piece (domainGraph (FrameDomain F)) :=
    mapPiece iso.toHom (rawPieces i)
  have hlist : List.ofFn pieces = (List.ofFn rawPieces).map (mapPiece iso.toHom) := by
    rw [List.map_ofFn]
    rfl
  obtain ⟨_, hp, hs', he', hc'⟩ := actual_cycle_partition_map iso.toHom
    iso.toEquiv.injective rawWalk hraw.isCycle (List.ofFn rawPieces)
    (actualJointCuts (F2Domain m)) hs he hc
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

#print axioms native_actual_j2_joint_paths
#print axioms native_actual_j2_frame_joint_paths

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2JointPaths
