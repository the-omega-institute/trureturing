/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualStatePromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recover the original P opening on the same actual parent. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
import D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

set_option autoImplicit false
-- Preserve definitional identities of the saved dependent child domains.
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStatePromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualPJointPrefix
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private linked_of_getElem finish_eq_last from
  D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering
open private pChildIndex outer_base_bound old_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private map_filtered_complement from
  D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open private actual_joint_split_cut_inventory from
  D5.S3.Combinatorics.Graph.Walks.ActualJointHalfCutInventory

/-- The actual ordinary opening in the parent retains the original P
supplier's full joint support and exactly its original uncut edges.
The old joint cuts are restored before removing this particular supplier
edge; each inventory refers to W.P, W.oldP and W.paths simultaneously. -/
private theorem original_state_p_opening_inventory {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA) :
    let O := outerFrame F A u hbase
    let j := pChildIndex F A u hbase
    let opening := (W.paths j).piece.walk
    let jointEdges := (⟨W.P.left, W.P.far, W.P.distinguished⟩ :: ⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest).flatMap fun p => p.walk.edges
    let jointSupport := (⟨W.P.left, W.P.far, W.P.distinguished⟩ :: ⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest).flatMap fun p => p.walk.support
    let cut := s(rightPort O (k + j.val), leftPort O (k + j.val))
    (opening.support.map Subtype.val).Perm (jointSupport.map Subtype.val) ∧
      (opening.edges.map (Sym2.map Subtype.val)).Perm
        ((W.P.walk.edges.map (Sym2.map Subtype.val)).filter
          fun e => decide (e ≠ cut)) ∧
      (opening.edges.map (Sym2.map Subtype.val)).Perm
        (((jointEdges ++ W.P.H.toList ++ W.P.K.toList).map
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
  have hcut (f) : f ∈ q.edges ↔ f ∈ W.oldP.walk.edges ∧ f ≠ e := by
    have h := W.ordinaryInventory j hj f
    rw [W.oldPAttached] at h
    exact h
  have hs : q.support.Perm W.oldP.walk.support.tail := by
    apply List.perm_iff_count.mpr
    intro x
    simpa only [List.count_eq_countP, Bool.beq_eq_decide_eq] using
      ((W.paths j).hamiltonian x).trans
      ((SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.mp
        W.oldP.hamiltonian).2 x).symm
  have he : q.edges.Perm (W.oldP.walk.edges.filter fun f => decide (f ≠ e)) := by
    apply (List.perm_ext_iff_of_nodup
      (W.paths j).hamiltonian.isPath.isTrail.edges_nodup
      (W.oldP.hamiltonian.isCycle.isTrail.edges_nodup.filter _)).mpr
    intro f
    simp only [List.mem_filter, decide_eq_true_eq]
    exact hcut f
  have hrawSupport : W.oldP.walk.support.map Subtype.val =
      W.P.walk.support.map Subtype.val := by
    have h := congrArg (fun z => z.support.map Subtype.val) W.oldPWalk
    simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map,
      List.map_map, Function.comp_def, pMarkedChildMap, RelHom.coeFn_mk] using h
  have hrawEdges : W.oldP.walk.edges.map (Sym2.map Subtype.val) =
      W.P.walk.edges.map (Sym2.map Subtype.val) := by
    have h := congrArg (fun z => z.edges.map (Sym2.map Subtype.val)) W.oldPWalk
    simpa only [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_map,
      List.map_map, Function.comp_def, Sym2.map_map, pMarkedChildMap, RelHom.coeFn_mk] using h
  have htail : W.oldP.walk.support.tail.map Subtype.val =
      W.P.walk.support.tail.map Subtype.val := by
    simpa only [List.map_tail] using congrArg List.tail hrawSupport
  have hsraw : (q.support.map Subtype.val).Perm
      (W.P.walk.support.tail.map Subtype.val) := by
    rw [← htail]
    exact hs.map Subtype.val
  have hsJoint := W.P.partitions.joint_partition.support.map Subtype.val
  have hefilter : (W.oldP.walk.edges.filter fun f => decide (f ≠ e)).map
      (Sym2.map Subtype.val) =
      (W.oldP.walk.edges.map (Sym2.map Subtype.val)).filter
        fun f => decide (f ≠ Sym2.map Subtype.val e) := by
    simpa only [Finset.mem_singleton, Finset.image_singleton] using
      map_filtered_complement (Sym2.map Subtype.val)
        (Sym2.map.injective Subtype.val_injective) W.oldP.walk.edges {e}
  have heraw := he.map (Sym2.map Subtype.val)
  rw [hefilter, hrawEdges] at heraw
  have heval : Sym2.map Subtype.val e =
      s(rightPort O (k + j.val), leftPort O (k + j.val)) := rfl
  rw [heval] at heraw
  have hwhole := actual_joint_split_cut_inventory W.P.walk
    W.P.hamiltonian.isCycle
    ((⟨W.P.left, W.P.far, W.P.distinguished⟩ :: ⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest).flatMap fun p => p.walk.edges)
    W.P.K W.P.H W.P.partitions.disjoint
    W.P.partitions.joint_partition.edges W.P.partitions.joint_partition.cut_mem
  have hrawWhole := (hwhole.map (Sym2.map Subtype.val)).filter
    (fun f => decide (f ≠ s(rightPort O (k + j.val), leftPort O (k + j.val))))
  exact ⟨hsraw.trans hsJoint.symm, heraw, heraw.trans hrawWhole⟩

#print axioms original_state_p_opening_inventory


/-- The two literal P prefix edges and the exact post-opening edge
inventory are derived from the original strong state and same parent. -/
private theorem original_state_p_joint_split {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA) :
    let O := outerFrame F A u hbase
    let opening := (W.paths (pChildIndex F A u hbase)).piece.walk
    let d := W.P.distinguished
    let rest := ⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest
    ∃ (s t : {x : Configuration m // SpecialDomain F (old_base_bound F A u hbase hA) x}),
      s.val = rightPort O (m - 1) ∧ t.val = leftPort O (m - 1) ∧
      ∃ (hₐ : (domainGraph (SpecialDomain F (old_base_bound F A u hbase hA))).Adj W.P.left s)
        (h_b : (domainGraph (SpecialDomain F (old_base_bound F A u hbase hA))).Adj s t)
        (tail : (domainGraph (SpecialDomain F (old_base_bound F A u hbase hA))).Walk t W.P.far),
        d = (tail.cons h_b).cons hₐ ∧ tail.IsPath ∧
        (opening.support.map Subtype.val).Perm
          ((d.support ++ rest.flatMap fun p => p.walk.support).map Subtype.val) ∧
        (opening.edges.map (Sym2.map Subtype.val)).Perm
          (((rest.flatMap fun p => p.walk.edges) ++ tail.edges ++
            [s(W.P.left, s)] ++ W.P.H.toList ++ W.P.K.toList).map (Sym2.map Subtype.val)) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let j := pChildIndex F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let hBF := old_base_bound F A u hbase hA
  have hj : 0 < j.val := by change 0 < A.length; omega
  have hidx : k + j.val = m - 1 := by
    have h := F.prefix_length
    rw [hbase, List.length_append, F.selected_length,
      List.length_append, List.length_singleton] at h
    change k + A.length = m - 1
    omega
  let r := ordinaryRight hm O hBO j hj
  let l := ordinaryLeft hm O hBO j hj
  let s : {x : Configuration m // SpecialDomain F hBF x} := ⟨r.val,
    (native_p_marked_domain_eq_child F A u hbase hA r.val).mpr r.property⟩
  let t : {x : Configuration m // SpecialDomain F hBF x} := ⟨l.val,
    (native_p_marked_domain_eq_child F A u hbase hA l.val).mpr l.property⟩
  have hs : s.val = rightPort O (m - 1) := by
    change rightPort O (k + j.val) = _
    rw [hidx]
  have ht : t.val = leftPort O (m - 1) := by
    change leftPort O (k + j.val) = _
    rw [hidx]
  let d := W.P.distinguished
  let rest := ⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest
  have hn : (d.support ++ rest.flatMap fun p => p.walk.support).Nodup :=
    W.P.partitions.joint_partition.support.nodup_iff.mpr W.P.hamiltonian.isCycle.support_nodup
  have hK : (W.P.K ∪ W.P.H).image (Sym2.map Subtype.val) =
      markedCuts F ∪ markedCuts W.P.oppositeFrame := by
    rw [Finset.image_union, W.P.primaryCuts, W.P.oppositeCuts]
  have hinv (e) : e ∈ ((⟨W.P.left, W.P.far, d⟩ :: rest).flatMap fun p => p.walk.edges) ↔
      e ∈ W.P.walk.edges ∧ e ∉ W.P.K ∪ W.P.H := by
    rw [W.P.partitions.joint_partition.edges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  have hsa : s.val = W.P.left.val * a m := by
    rw [hs, W.P.leftCoordinate]
    exact (native_p_parent_cut_prefix hm F A u hbase).1.symm
  have htb : t.val = s.val * b m := by rw [ht, hs]; rfl
  have hprot := native_protected_labels F hk
  obtain ⟨hₐ, h_b, tail, hd, htail, _, hde⟩ :=
    native_actual_p_joint_prefix hm F W.P.oppositeFrame A u hbase W.P.sameTerminal
      (protectedP F hk) (protectedQ F hk)
      (List.mem_toFinset.mpr hprot.2.1) (List.mem_toFinset.mpr hprot.2.2.1)
      (SpecialDomain F hBF) W.P.walk W.P.keepsProtectedA W.P.keepsRemainingB
      d rest hn (W.P.K ∪ W.P.H) hK hinv W.P.leftCoordinate hsa htb
  let remaining := (rest.flatMap fun p => p.walk.edges) ++ tail.edges ++
    [s(W.P.left, s)] ++ W.P.H.toList ++ W.P.K.toList
  have hwhole := actual_joint_split_cut_inventory W.P.walk
    W.P.hamiltonian.isCycle
    ((⟨W.P.left, W.P.far, d⟩ :: rest).flatMap fun p => p.walk.edges)
    W.P.K W.P.H W.P.partitions.disjoint
    W.P.partitions.joint_partition.edges W.P.partitions.joint_partition.cut_mem
  have hwhole' : W.P.walk.edges.Perm (s(s, t) :: remaining) := by
    apply hwhole.trans
    change ((d.edges ++ rest.flatMap fun p => p.walk.edges) ++
      W.P.H.toList ++ W.P.K.toList).Perm (s(s, t) :: remaining)
    rw [hde]
    apply List.perm_iff_count.mpr
    intro e
    simp only [remaining, List.count_append, List.count_cons, List.count_nil,
      List.count_singleton]
    omega
  have hnot : s(s, t) ∉ remaining :=
    (List.nodup_cons.mp (hwhole'.nodup_iff.mp
      W.P.hamiltonian.isCycle.isTrail.edges_nodup)).1
  have hfiltered : (W.P.walk.edges.filter fun e => decide (e ≠ s(s, t))).Perm remaining := by
    have hf := hwhole'.filter (fun e => decide (e ≠ s(s, t)))
    have hr : remaining.filter (fun e => decide (e ≠ s(s, t))) = remaining := by
      apply List.filter_eq_self.mpr
      intro e he
      exact decide_eq_true (fun heq => hnot (heq ▸ he))
    simpa only [List.filter_cons, ne_eq, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, hr] using hf
  have hmapfilter : (W.P.walk.edges.filter fun e => decide (e ≠ s(s, t))).map
      (Sym2.map Subtype.val) =
      (W.P.walk.edges.map (Sym2.map Subtype.val)).filter
        (fun e => decide (e ≠ s(s.val, t.val))) := by
    simpa only [Finset.mem_singleton, Finset.image_singleton, Sym2.map_mk] using
      map_filtered_complement (Sym2.map Subtype.val)
        (Sym2.map.injective Subtype.val_injective) W.P.walk.edges {s(s, t)}
  obtain ⟨hopenS, hopenE, _⟩ := original_state_p_opening_inventory hm hk F A u hbase hA W
  refine ⟨s, t, hs, ht, hₐ, h_b, tail, hd, htail, hopenS, ?_⟩
  have he := hfiltered.map (Sym2.map Subtype.val)
  rw [hmapfilter] at he
  have hcut : s(s.val, t.val) = s(rightPort O (k + j.val), leftPort O (k + j.val)) := rfl
  rw [hcut] at he
  exact hopenE.trans he

#print axioms original_state_p_joint_split

/-- The same saved child pieces have their literal native c connections.
This is the chain consumed by the actual joint update, including the
original P opening as its last piece and the saved parent base. -/
private theorem same_parent_chain {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA) :
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
      leftPort O (k + j.val) := by
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
      ((native_anchored_supply_coordinates (by omega : 3 ≤ m) O).1 (k + i)).2.2.2
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
  have hidx : k + (pChildIndex F A u hbase).val = m - 1 := by
    simp only [O, outerFrame, List.length_append, List.length_singleton] at hp
    change k + A.length = m - 1
    omega
  rw [hidx]
  exact (native_anchored_supply_coordinates (by omega : 3 ≤ m) O).2.2

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStatePromotion
