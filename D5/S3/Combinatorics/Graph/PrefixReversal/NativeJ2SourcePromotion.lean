/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SourcePromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Earn old P joint prefixes and exact inventories from the same saved supplier. -/
/- Candidate source-promotion companion. This file has not yet been
   kernel checked and is not part of the narrow parent delivery.
   The goal is to derive the original P opening inventories from one
   retained RawSeedFor, not choose a replacement child witness. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
import D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2HalfRestoration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2HalfPaths
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJ2JointPaths
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open private parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private linked_of_getElem finish_eq_last from
  D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering
open private pChildIndex outer_base_bound old_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private j2_frame_special_domain j2SpecialMap from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
open private map_filtered_complement from
  D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open private actual_joint_split_cut_inventory from
  D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

private noncomputable def rawSideCut {m : ℕ} (hm : 5 ≤ m) (side : Bool)
    (i : Fin 3) : Sym2 {x : Configuration m // F2Domain m x} :=
  s(⟨port m (i, side, false), native_j2_port_domain hm _⟩,
    ⟨port m (i, side, true), native_j2_port_domain hm _⟩)

private theorem raw_side_cuts {m : ℕ} (hm : 5 ≤ m) (side : Bool) :
    actualHalfCuts (F2Domain m) side = Finset.univ.image (rawSideCut hm side) := by
  classical
  ext e
  change (e ∈ Finset.univ.filter (fun z : Sym2 {x : Configuration m // F2Domain m x} =>
    HalfCut m side (Sym2.map Subtype.val z))) ↔ _
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, i, hi⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Sym2.map.injective Subtype.val_injective
    simpa only [rawSideCut, Sym2.map_mk, markedEdge] using hi.symm
  · rintro ⟨i, _, rfl⟩
    exact ⟨Finset.mem_univ _, i, rfl⟩

/-- Both literal old marked groups come from this same retained raw seed.
The opposite group uses the reversed selected frame at exactly the same
indices; neither the terminal nor the base is changed. -/
private theorem same_seed_marked_cut_images {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (P : RawSeedFor hm F) :
    P.seed.K.image (Sym2.map Subtype.val) = markedCuts F ∧
      P.seed.H.image (Sym2.map Subtype.val) = markedCuts (reverseSelected F) := by
  classical
  constructor
  · rw [P.primaryCuts, raw_side_cuts hm false]
    dsimp only [FrameDomain]
    simp only [Finset.image_image, markedCuts]
    apply Finset.image_congr
    intro i _
    change s(relabel F * port m (i, false, false), relabel F * port m (i, false, true)) =
      s(rightPort F i.val, leftPort F i.val)
    simp only [port, Bool.false_eq_true, ↓reduceIte]
    rw [(native_j2_frame_ports hm F i).1, (native_j2_frame_ports hm F i).2]
  · rw [P.oppositeCuts, raw_side_cuts hm true]
    dsimp only [FrameDomain]
    simp only [Finset.image_image, markedCuts]
    apply Finset.image_congr
    intro i _
    change s(relabel F * port m (i, true, false), relabel F * port m (i, true, true)) =
      s(rightPort (reverseSelected F) i.val, leftPort (reverseSelected F) i.val)
    simp only [port, Bool.false_eq_true, ↓reduceIte]
    rw [(native_j2_frame_barred_ports hm F i).1, (native_j2_frame_barred_ports hm F i).2]

/-- The actual ordinary opening in the parent retains the original P
supplier's full joint support and exactly its original uncut edges.
The old joint cuts are restored before removing this particular supplier
edge; each inventory refers to W.P, W.oldP and W.paths simultaneously. -/
theorem native_j2_original_p_opening_inventory {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let O := outerFrame F A u hbase
    let j := pChildIndex F A u hbase
    let opening := (W.paths j).piece.walk
    let jointEdges := (List.ofFn W.P.seed.joint).flatMap fun p => p.walk.edges
    let jointSupport := (List.ofFn W.P.seed.joint).flatMap fun p => p.walk.support
    let cut := s(rightPort O (2 + j.val), leftPort O (2 + j.val))
    (opening.support.map Subtype.val).Perm (jointSupport.map Subtype.val) ∧
      (opening.edges.map (Sym2.map Subtype.val)).Perm
        ((W.P.seed.walk.edges.map (Sym2.map Subtype.val)).filter
          fun e => decide (e ≠ cut)) ∧
      (opening.edges.map (Sym2.map Subtype.val)).Perm
        (((jointEdges ++ W.P.seed.H.toList ++ W.P.seed.K.toList).map
          (Sym2.map Subtype.val)).filter fun e => decide (e ≠ cut)) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let j := pChildIndex F A u hbase
  have hj : 0 < j.val := by change 0 < A.length; omega
  let hBO := outer_base_bound F A u hbase hA
  let q := (W.paths j).piece.walk
  let e := s(ordinaryRight (by omega : 3 ≤ m) O hBO j hj,
    ordinaryLeft (by omega : 3 ≤ m) O hBO j hj)
  have hcut (f) : f ∈ q.edges ↔ f ∈ W.oldP.cycle.walk.edges ∧ f ≠ e := by
    have h := W.ordinaryInventory j hj f
    rw [W.oldPAttached] at h
    exact h
  have hs : q.support.Perm W.oldP.cycle.walk.support.tail := by
    apply List.perm_iff_count.mpr
    intro x
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      ((W.paths j).hamiltonian x).trans
      ((SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp
        W.oldP.cycle.hamiltonian).2 x).symm
  have he : q.edges.Perm (W.oldP.cycle.walk.edges.filter fun f => decide (f ≠ e)) := by
    apply (List.perm_ext_iff_of_nodup
      (W.paths j).hamiltonian.isPath.isTrail.edges_nodup
      (W.oldP.cycle.hamiltonian.isCycle.isTrail.edges_nodup.filter _)).mpr
    intro f
    simp only [List.mem_filter, decide_eq_true_eq]
    exact hcut f
  have hrawSupport : W.oldP.cycle.walk.support.map Subtype.val =
      W.P.seed.walk.support.map Subtype.val := by
    have h := congrArg (fun z => z.support.map Subtype.val) W.oldP.mappedWalk
    simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.map_map, Function.comp_def, pMarkedChildMap, j2SpecialMap,
      RelHom.coeFn_mk] using h
  have hrawEdges : W.oldP.cycle.walk.edges.map (Sym2.map Subtype.val) =
      W.P.seed.walk.edges.map (Sym2.map Subtype.val) := by
    have h := congrArg (fun z => z.edges.map (Sym2.map Subtype.val)) W.oldP.mappedWalk
    simpa only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
      List.map_map, Function.comp_def, Sym2.map_map, pMarkedChildMap, j2SpecialMap,
      RelHom.coeFn_mk] using h
  have htail : W.oldP.cycle.walk.support.tail.map Subtype.val =
      W.P.seed.walk.support.tail.map Subtype.val := by
    simpa only [List.map_tail] using congrArg List.tail hrawSupport
  have hsraw : (q.support.map Subtype.val).Perm
      (W.P.seed.walk.support.tail.map Subtype.val) := by
    rw [← htail]
    exact hs.map Subtype.val
  have hsJoint := W.P.seed.partitions.joint_partition.support.map Subtype.val
  have hefilter : (W.oldP.cycle.walk.edges.filter fun f => decide (f ≠ e)).map
      (Sym2.map Subtype.val) =
      (W.oldP.cycle.walk.edges.map (Sym2.map Subtype.val)).filter
        fun f => decide (f ≠ Sym2.map Subtype.val e) := by
    simpa only [Finset.mem_singleton, Finset.image_singleton] using
      map_filtered_complement (Sym2.map Subtype.val)
        (Sym2.map.injective Subtype.val_injective) W.oldP.cycle.walk.edges {e}
  have heraw := he.map (Sym2.map Subtype.val)
  rw [hefilter, hrawEdges] at heraw
  have heval : Sym2.map Subtype.val e =
      s(rightPort O (2 + j.val), leftPort O (2 + j.val)) := rfl
  rw [heval] at heraw
  have hwhole := actual_joint_split_cut_inventory W.P.seed.walk
    W.P.seed.hamiltonian.isCycle
    ((List.ofFn W.P.seed.joint).flatMap fun p => p.walk.edges)
    W.P.seed.K W.P.seed.H W.P.seed.partitions.disjoint
    W.P.seed.partitions.joint_partition.edges W.P.seed.partitions.joint_partition.cut_mem
  have hrawWhole := (hwhole.map (Sym2.map Subtype.val)).filter
    (fun f => decide (f ≠ s(rightPort O (2 + j.val), leftPort O (2 + j.val))))
  exact ⟨hsraw.trans hsJoint.symm, heraw, heraw.trans hrawWhole⟩

#print axioms native_j2_original_p_opening_inventory

/-- The old distinguished component is an actual piece of the retained P
seed. Its first two edges are earned from the original a/b invariants,
and the second is exactly the supplier edge removed by this parent's P
opening. The support and remaining-edge permutations are therefore the
actual inputs required by the next joint-partition update. -/
theorem native_j2_original_p_joint_split {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let O := outerFrame F A u hbase
    let j := pChildIndex F A u hbase
    let d := (W.P.seed.joint 1).walk
    let rest := [W.P.seed.joint 0, W.P.seed.joint 2, W.P.seed.joint 3,
      W.P.seed.joint 4, W.P.seed.joint 5]
    let opening := (W.paths j).piece.walk
    ∃ s t : {x : Configuration m // FrameDomain F x},
      s.val = rightPort O (m - 1) ∧ t.val = leftPort O (m - 1) ∧
      ∃ (hₐ : (domainGraph (FrameDomain F)).Adj (W.P.seed.joint 1).start s)
        (h_b : (domainGraph (FrameDomain F)).Adj s t)
        (tail : (domainGraph (FrameDomain F)).Walk t (W.P.seed.joint 1).finish),
        d = (tail.cons h_b).cons hₐ ∧ tail.IsPath ∧
        (opening.support.map Subtype.val).Perm
          ((d.support ++ rest.flatMap fun p => p.walk.support).map Subtype.val) ∧
        (opening.edges.map (Sym2.map Subtype.val)).Perm
          (((rest.flatMap fun p => p.walk.edges) ++ tail.edges ++
            [s((W.P.seed.joint 1).start, s)] ++ W.P.seed.H.toList ++
            W.P.seed.K.toList).map (Sym2.map Subtype.val)) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let j := pChildIndex F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let hBF := old_base_bound F A u hbase hA
  have hj : 0 < j.val := by change 0 < A.length; omega
  have hidx : 2 + j.val = m - 1 := by
    have h := F.prefix_length
    rw [hbase, List.length_append, F.selected_length,
      List.length_append, List.length_singleton] at h
    change 2 + A.length = m - 1
    omega
  let r := ordinaryRight (by omega : 3 ≤ m) O hBO j hj
  let l := ordinaryLeft (by omega : 3 ≤ m) O hBO j hj
  let s : {x : Configuration m // FrameDomain F x} := ⟨r.val,
    (j2_frame_special_domain F hBF r.val).mpr
      ((native_p_marked_domain_eq_child F A u hbase hA r.val).mpr r.property)⟩
  let t : {x : Configuration m // FrameDomain F x} := ⟨l.val,
    (j2_frame_special_domain F hBF l.val).mpr
      ((native_p_marked_domain_eq_child F A u hbase hA l.val).mpr l.property)⟩
  have hs : s.val = rightPort O (m - 1) := by
    change rightPort O (2 + j.val) = _
    rw [hidx]
  have ht : t.val = leftPort O (m - 1) := by
    change leftPort O (2 + j.val) = _
    rw [hidx]
  let d := (W.P.seed.joint 1).walk
  let rest := [W.P.seed.joint 0, W.P.seed.joint 2, W.P.seed.joint 3,
    W.P.seed.joint 4, W.P.seed.joint 5]
  have hp : (W.P.seed.joint 1 :: rest).Perm (List.ofFn W.P.seed.joint) := by
    change [W.P.seed.joint 1, W.P.seed.joint 0, W.P.seed.joint 2,
      W.P.seed.joint 3, W.P.seed.joint 4, W.P.seed.joint 5].Perm
      [W.P.seed.joint 0, W.P.seed.joint 1, W.P.seed.joint 2,
        W.P.seed.joint 3, W.P.seed.joint 4, W.P.seed.joint 5]
    exact List.Perm.swap _ _ _
  have hps := hp.flatMap_right (fun p => p.walk.support)
  have hpe := hp.flatMap_right (fun p => p.walk.edges)
  have hn : (d.support ++ rest.flatMap fun p => p.walk.support).Nodup := by
    exact hps.nodup_iff.mpr
      (W.P.seed.partitions.joint_partition.support.nodup_iff.mpr
        W.P.seed.hamiltonian.isCycle.support_nodup)
  have hK : (W.P.seed.K ∪ W.P.seed.H).image (Sym2.map Subtype.val) =
      markedCuts F ∪ markedCuts (reverseSelected F) := by
    rw [Finset.image_union, (same_seed_marked_cut_images hm F W.P).1,
      (same_seed_marked_cut_images hm F W.P).2]
  have hinv (e) : e ∈ ((W.P.seed.joint 1 :: rest).flatMap fun p => p.walk.edges) ↔
      e ∈ W.P.seed.walk.edges ∧ e ∉ W.P.seed.K ∪ W.P.seed.H := by
    rw [hpe.mem_iff, W.P.seed.partitions.joint_partition.edges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  have hℓ : (W.P.seed.joint 1).start.val = leftPort F 0 := by
    have h := (W.P.seed.jointPorts 1).1
    change (W.P.seed.joint 1).start.val = relabel F * port m (0, false, true) at h
    rw [h]
    simpa only [port, Bool.false_eq_true, ↓reduceIte, Fin.val_zero] using
      (native_j2_frame_ports hm F 0).2
  have hsa : s.val = (W.P.seed.joint 1).start.val * a m := by
    rw [hs, hℓ]
    exact (native_p_parent_cut_prefix (by omega : 3 ≤ m) F A u hbase).1.symm
  have htb : t.val = s.val * b m := by rw [ht, hs]; rfl
  have hprot := native_protected_labels F (by omega : 2 ≤ 2)
  obtain ⟨hₐ, h_b, tail, hd, htail, _, hde⟩ :=
    native_actual_p_joint_prefix (by omega : 3 ≤ m) F (reverseSelected F) A u hbase rfl
      (protectedP F (by omega)) (protectedQ F (by omega))
      (List.mem_toFinset.mpr hprot.2.1) (List.mem_toFinset.mpr hprot.2.2.1)
      (FrameDomain F) W.P.seed.walk W.P.seed.keepsProtectedA W.P.seed.keepsRemainingB
      d rest hn (W.P.seed.K ∪ W.P.seed.H) hK hinv hℓ hsa htb
  let remaining := (rest.flatMap fun p => p.walk.edges) ++ tail.edges ++
    [s((W.P.seed.joint 1).start, s)] ++ W.P.seed.H.toList ++ W.P.seed.K.toList
  have hwhole := actual_joint_split_cut_inventory W.P.seed.walk
    W.P.seed.hamiltonian.isCycle
    ((List.ofFn W.P.seed.joint).flatMap fun p => p.walk.edges)
    W.P.seed.K W.P.seed.H W.P.seed.partitions.disjoint
    W.P.seed.partitions.joint_partition.edges W.P.seed.partitions.joint_partition.cut_mem
  have hwhole' : W.P.seed.walk.edges.Perm (s(s, t) :: remaining) := by
    apply hwhole.trans
    apply (hpe.symm.append_right W.P.seed.H.toList |>.append_right W.P.seed.K.toList).trans
    change ((d.edges ++ rest.flatMap fun p => p.walk.edges) ++
      W.P.seed.H.toList ++ W.P.seed.K.toList).Perm (s(s, t) :: remaining)
    rw [hde]
    apply List.perm_iff_count.mpr
    intro e
    simp only [remaining, List.count_append, List.count_cons, List.count_nil,
      List.count_singleton]
    omega
  have hnot : s(s, t) ∉ remaining :=
    (List.nodup_cons.mp (hwhole'.nodup_iff.mp
      W.P.seed.hamiltonian.isCycle.isTrail.edges_nodup)).1
  have hfiltered : (W.P.seed.walk.edges.filter fun e => decide (e ≠ s(s, t))).Perm
      remaining := by
    have hf := hwhole'.filter (fun e => decide (e ≠ s(s, t)))
    have hr : remaining.filter (fun e => decide (e ≠ s(s, t))) = remaining := by
      apply List.filter_eq_self.mpr
      intro e he
      exact decide_eq_true (fun heq => hnot (heq ▸ he))
    simpa only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, hr] using hf
  have hmapfilter : (W.P.seed.walk.edges.filter fun e => decide (e ≠ s(s, t))).map
      (Sym2.map Subtype.val) =
      (W.P.seed.walk.edges.map (Sym2.map Subtype.val)).filter
        (fun e => decide (e ≠ s(s.val, t.val))) := by
    simpa only [Finset.mem_singleton, Finset.image_singleton, Sym2.map_mk] using
      map_filtered_complement (Sym2.map Subtype.val)
        (Sym2.map.injective Subtype.val_injective) W.P.seed.walk.edges {s(s, t)}
  obtain ⟨hopenS, hopenE, _⟩ := native_j2_original_p_opening_inventory hm F A u hbase hA W
  refine ⟨s, t, hs, ht, hₐ, h_b, tail, hd, htail, ?_, ?_⟩
  · exact hopenS.trans (hps.map Subtype.val).symm
  · have he := hfiltered.map (Sym2.map Subtype.val)
    rw [hmapfilter] at he
    have hcut : s(s.val, t.val) = s(rightPort O (2 + j.val), leftPort O (2 + j.val)) := rfl
    rw [hcut] at he
    exact hopenE.trans he

#print axioms native_j2_original_p_joint_split

/-- The same saved child pieces have their literal native c connections.
This is the chain consumed by the actual joint update, including the
original P opening as its last piece and the saved parent base. -/
private theorem same_parent_chain {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let O := outerFrame F A u hbase
    let p := W.pieces ⟨0, by
      simp only [O, outerFrame, List.length_append, List.length_singleton]; omega⟩
    let ps := List.ofFn fun i : Fin (O.base.length - 1) =>
      W.pieces ⟨i.val + 1, by
        have hi := i.isLt
        simp only [O, outerFrame, List.length_append, List.length_singleton] at hi ⊢
        omega⟩
    W.base = p.start ∧ Linked p ps ∧
      finish p ps = (W.pieces (pChildIndex F A u hbase)).finish ∧
      (domainGraph (ParentDomain O)).Adj
        (W.pieces (pChildIndex F A u hbase)).finish W.base := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let p := W.pieces ⟨0, by
    simp only [O, outerFrame, List.length_append, List.length_singleton]; omega⟩
  let ps := List.ofFn fun i : Fin (O.base.length - 1) =>
    W.pieces ⟨i.val + 1, by
      have hi := i.isLt
      simp only [O, outerFrame, List.length_append, List.length_singleton] at hi ⊢
      omega⟩
  have hlen : 3 ≤ O.base.length := outer_base_bound F A u hbase hA
  have hlist : p :: ps = List.ofFn W.pieces := by
    apply List.ext_getElem
    · simp only [ps, List.length_cons, List.length_ofFn]
      change O.base.length - 1 + 1 = O.base.length
      omega
    · intro i hi hj
      cases i with
      | zero => simp only [p, List.getElem_cons_zero, List.getElem_ofFn]
      | succ i => simp only [ps, List.getElem_cons_succ, List.getElem_ofFn]
  have hstart (j : Fin O.base.length) : (W.pieces j).start.val =
      rightPort O (childStartIndex O j) := by
    rw [W.childPieces]
    exact (W.paths j).start_eq
  have hfinish (j : Fin O.base.length) : (W.pieces j).finish.val =
      leftPort O (2 + j.val) := by
    rw [W.childPieces]
    exact (W.paths j).finish_eq
  have hb : W.base = p.start := by
    apply Subtype.ext
    rw [W.baseCoordinate]
    symm
    simpa only [p, childStartIndex, Fin.val_mk, if_pos rfl, ite_true] using
      hstart ⟨0, by omega⟩
  have hlinked : Linked p ps := by
    apply linked_of_getElem
    intro i hi
    simp only [hlist, List.length_ofFn] at hi
    change i + 1 < O.base.length at hi
    have hi₁ : i + 1 < (outerFrame F A u hbase).base.length := hi
    have hi₀ : i < (outerFrame F A u hbase).base.length :=
      Nat.lt_trans (Nat.lt_succ_self i) hi₁
    simp only [hlist, List.getElem_ofFn]
    change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
      (W.pieces ⟨i, hi₀⟩).finish.val (W.pieces ⟨i + 1, hi₁⟩).start.val
    rw [hfinish ⟨i, hi₀⟩, hstart ⟨i + 1, hi₁⟩]
    simp only [childStartIndex, Fin.val_mk, if_neg (by omega : ¬ i + 1 = 0)]
    simpa only [Nat.add_assoc] using
      ((native_anchored_supply_coordinates (by omega : 3 ≤ m) O).1 (2 + i)).2.2.2
  have hlastIndex : (⟨O.base.length - 1, by omega⟩ : Fin O.base.length) =
      pChildIndex F A u hbase := by
    apply Fin.ext
    simp only [O, outerFrame, List.length_append, List.length_singleton, pChildIndex]
    omega
  have hlast : finish p ps = (W.pieces (pChildIndex F A u hbase)).finish := by
    have hne : List.ofFn W.pieces ≠ [] := by
      intro h
      have hlength := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at hlength
      change O.base.length = 0 at hlength
      omega
    have hget := List.getLast_congr (by simp : p :: ps ≠ []) hne hlist
    have h := (finish_eq_last p ps).trans (congrArg Piece.finish hget)
    simp only [List.getLast_ofFn] at h
    have hi : (⟨(outerFrame F A u hbase).base.length - 1, by
        change O.base.length - 1 < O.base.length; omega⟩ :
        Fin (outerFrame F A u hbase).base.length) = pChildIndex F A u hbase := hlastIndex
    simpa only [hi] using h
  refine ⟨hb, hlinked, hlast, ?_⟩
  rw [hb]
  change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
    (W.pieces (pChildIndex F A u hbase)).finish.val p.start.val
  rw [hfinish]
  have hpstart : p.start.val = rightPort O 0 := by
    simpa only [p, childStartIndex, Fin.val_mk, if_pos rfl, ite_true] using
      hstart ⟨0, by omega⟩
  rw [hpstart]
  have hp := O.prefix_length
  simp only [List.length_append, O.selected_length] at hp
  have hidx : 2 + (pChildIndex F A u hbase).val = m - 1 := by
    simp only [O, outerFrame, List.length_append, List.length_singleton] at hp
    change 2 + A.length = m - 1
    omega
  rw [hidx]
  exact (native_anchored_supply_coordinates (by omega : 3 ≤ m) O).2.2

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
