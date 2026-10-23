/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2JointPromotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2JointPromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Promote the original P and Q paths on their same actual native J2 parent. -/
/- Candidate source, not yet kernel checked or admitted for freezing.
   The private transport below is intended for the actual eight-piece
   joint constructor, not as a separately delivered application. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2QSourcePromotion
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2JointPromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Components
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2QSourcePromotion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open private pChildIndex old_base_bound outer_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private j2SpecialMap from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentCycle
open private childLift parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private same_parent_chain from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
open private same_seed_marked_cut_images from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SourcePromotion
open private special_child_path from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep

private def rawPParentMap {m : ℕ} (F : SupplyFrame m 2)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    domainGraph (FrameDomain F) →g ParentGraph F A u hbase :=
  (pMarkedParentLift F A u hbase hA).comp
    (j2SpecialMap F (old_base_bound F A u hbase hA))

private theorem piece_copy_eq {V : Type*} {G : SimpleGraph V}
    (p : Piece G) (a b : V) (ha : p.start = a) (hb : p.finish = b) :
    (⟨a, b, p.walk.copy ha hb⟩ : Piece G) = p := by
  rcases p with ⟨x, y, w⟩
  dsimp only at ha hb
  subst a
  subst b
  rfl

private theorem same_old_joint_native_ports {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) (i : Fin 6) :
    let old := mapPiece (rawPParentMap F A u hbase hA) (W.P.seed.joint i)
    old.start.val = ![rightPort F 0, leftPort F 0, rightPort F 1,
      leftPort F 2, rightPort (reverseSelected F) 0, leftPort F 1] i ∧
    old.finish.val = ![rightPort F 2, leftPort (reverseSelected F) 1,
      leftPort (reverseSelected F) 2, rightPort (reverseSelected F) 2,
      rightPort (reverseSelected F) 1, leftPort (reverseSelected F) 0] i := by
  let B := reverseSelected F
  have hR (j : Fin 3) : relabel F * port m (j, false, false) = rightPort F j.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte] using
      (native_j2_frame_ports hm F j).1
  have hL (j : Fin 3) : relabel F * port m (j, false, true) = leftPort F j.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte] using
      (native_j2_frame_ports hm F j).2
  have hBR (j : Fin 3) : relabel F * port m (j, true, false) = rightPort B j.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte] using
      (native_j2_frame_barred_ports hm F j).1
  have hBL (j : Fin 3) : relabel F * port m (j, true, true) = leftPort B j.val := by
    simpa only [port, Bool.false_eq_true, ↓reduceIte] using
      (native_j2_frame_barred_ports hm F j).2
  have h := W.P.seed.jointPorts i
  fin_cases i
  · exact ⟨h.1.trans (hR 0), h.2.trans (hR 2)⟩
  · exact ⟨h.1.trans (hL 0), h.2.trans (hBL 1)⟩
  · exact ⟨h.1.trans (hR 1), h.2.trans (hBL 2)⟩
  · exact ⟨h.1.trans (hL 2), h.2.trans (hBR 2)⟩
  · exact ⟨h.1.trans (hBR 0), h.2.trans (hBR 1)⟩
  · exact ⟨h.1.trans (hL 1), h.2.trans (hBL 0)⟩

/-- The literal P opening used in W has the transported split and exact
inventories of the original retained P seed. No new P path is selected. -/
private theorem same_p_parent_opening {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let O := outerFrame F A u hbase
    let lift := rawPParentMap F A u hbase hA
    let d := (W.P.seed.joint 1).walk.map lift
    let rest := [W.P.seed.joint 0, W.P.seed.joint 2, W.P.seed.joint 3,
      W.P.seed.joint 4, W.P.seed.joint 5].map (mapPiece lift)
    let deleted := (W.P.seed.H.toList ++ W.P.seed.K.toList).map (Sym2.map lift)
    ∃ s t : ParentVertex F A u hbase,
      s.val = rightPort O (m - 1) ∧ t.val = leftPort O (m - 1) ∧
      ∃ (hₐ : (ParentGraph F A u hbase).Adj (lift (W.P.seed.joint 1).start) s)
        (h_b : (ParentGraph F A u hbase).Adj s t)
        (tail : (ParentGraph F A u hbase).Walk t (lift (W.P.seed.joint 1).finish)),
        d = (tail.cons h_b).cons hₐ ∧
        ∃ P : (ParentGraph F A u hbase).Walk s t,
          (⟨s, t, P⟩ : Piece (ParentGraph F A u hbase)) =
            W.pieces (pChildIndex F A u hbase) ∧
          P.support.Perm (d.support ++ rest.flatMap fun p => p.walk.support) ∧
          P.edges.Perm ((rest.flatMap fun p => p.walk.edges) ++
            tail.edges ++ [s(lift (W.P.seed.joint 1).start, s)] ++ deleted) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let j := pChildIndex F A u hbase
  let lift := rawPParentMap F A u hbase hA
  obtain ⟨s₀, t₀, hs₀, ht₀, hₐ, h_b, tail, hd, _, hPs, hPe⟩ :=
    native_j2_original_p_joint_split hm F A u hbase hA W
  have hidx : 2 + j.val = m - 1 := by
    have h := F.prefix_length
    rw [hbase, List.length_append, F.selected_length,
      List.length_append, List.length_singleton] at h
    change 2 + A.length = m - 1
    omega
  have hj : 0 < j.val := by change 0 < A.length; omega
  have hs : (W.pieces j).start = lift s₀ := by
    apply Subtype.ext
    rw [W.childPieces]
    change (W.paths j).piece.start.val = s₀.val
    rw [(W.paths j).start_eq]
    simp only [childStartIndex, if_neg (by omega : ¬ j.val = 0), hidx, hs₀]
  have ht : (W.pieces j).finish = lift t₀ := by
    apply Subtype.ext
    rw [W.childPieces]
    change (W.paths j).piece.finish.val = t₀.val
    rw [(W.paths j).finish_eq, hidx, ht₀]
  let P := (W.pieces j).walk.copy hs ht
  refine ⟨lift s₀, lift t₀, hs₀, ht₀, lift.map_adj hₐ, lift.map_adj h_b,
    tail.map lift, ?_, P, ?_, ?_, ?_⟩
  · simpa only [SimpleGraph.Walk.map_cons] using congrArg
      (fun w => w.map lift) hd
  · exact piece_copy_eq (W.pieces j) _ _ hs ht
  · apply (List.map_perm_map_iff Subtype.val_injective).mp
    dsimp only [P]
    rw [SimpleGraph.Walk.support_copy, W.childPieces j]
    simpa only [parentPiece, childLift, lift, rawPParentMap, pMarkedParentLift,
      j2SpecialMap, SimpleGraph.Hom.comp, RelHom.comp_apply, RelHom.coeFn_mk, j,
      SimpleGraph.Walk.support_map,
      List.flatMap_map, mapPiece, List.map_append, List.map_map,
      List.map_flatMap, Function.comp_def, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.append_nil]
      using hPs
  · apply (List.map_perm_map_iff (Sym2.map.injective Subtype.val_injective)).mp
    dsimp only [P]
    rw [SimpleGraph.Walk.edges_copy, W.childPieces j]
    simpa only [parentPiece, childLift, lift, rawPParentMap, pMarkedParentLift,
      j2SpecialMap, SimpleGraph.Hom.comp, RelHom.comp_apply, RelHom.coeFn_mk, j,
      SimpleGraph.Walk.edges_map, List.flatMap_map, mapPiece,
      List.map_append, List.map_map, List.map_flatMap, List.map_cons, List.map_nil,
      Sym2.map_map, Sym2.map_mk, Function.comp_def, List.append_assoc,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using hPe

/-- Retain the literal saved first and last openings while exposing the
intervening list required by the closed-parent joint constructor. -/
private theorem same_parent_chain_inventory {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA)
    (p P : Piece (ParentGraph F A u hbase))
    (hp : p = W.pieces ⟨0, by
      simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩)
    (hP : P = W.pieces (pChildIndex F A u hbase)) :
    ∃ others : List (Piece (ParentGraph F A u hbase)),
      Linked p (others ++ [P]) ∧ W.base = p.start ∧
      (ParentGraph F A u hbase).Adj P.finish p.start ∧
      W.cycle.support.tail =
        ((p :: (others ++ [P])).flatMap fun z => z.walk.support).reverse ∧
      W.cycle.edges = s(W.base, finish p (others ++ [P])) ::
        (chainEdges p (others ++ [P])).reverse := by
  classical
  let O := outerFrame F A u hbase
  let p₀ := W.pieces ⟨0, by
    simp only [O, outerFrame, List.length_append, List.length_singleton]; omega⟩
  let ps := List.ofFn fun i : Fin (O.base.length - 1) =>
    W.pieces ⟨i.val + 1, by
      have hi := i.isLt
      simp only [O, outerFrame, List.length_append, List.length_singleton] at hi ⊢
      omega⟩
  have hlen : 3 ≤ O.base.length := outer_base_bound F A u hbase hA
  have hne : ps ≠ [] := by
    intro h
    have hlength := congrArg List.length h
    simp only [ps, List.length_ofFn, List.length_nil] at hlength
    omega
  have hlast : ps.getLast hne = W.pieces (pChildIndex F A u hbase) := by
    simp only [ps, List.getLast_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk, O, outerFrame, List.length_append,
      List.length_singleton, pChildIndex]
    omega
  have hps : ps = ps.dropLast ++ [P] := by
    rw [← hP] at hlast
    exact (List.dropLast_append_getLast hne).symm.trans
      (congrArg (fun q => ps.dropLast ++ [q]) hlast)
  have hlist : p₀ :: ps = List.ofFn W.pieces := by
    apply List.ext_getElem
    · simp only [ps, List.length_cons, List.length_ofFn]
      change O.base.length - 1 + 1 = O.base.length
      omega
    · intro i hi hj
      cases i with
      | zero => simp only [p₀, List.getElem_cons_zero, List.getElem_ofFn]
      | succ i => simp only [ps, List.getElem_cons_succ, List.getElem_ofFn]
  have hp₀ : p = p₀ := hp
  obtain ⟨hb, hlink, hfinish, hclose⟩ := same_parent_chain hm F A u hbase hA W
  change W.base = p₀.start at hb
  change Linked p₀ ps at hlink
  change finish p₀ ps = (W.pieces (pChildIndex F A u hbase)).finish at hfinish
  refine ⟨ps.dropLast, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hps, ← hp₀] at hlink
    exact hlink
  · simpa only [← hp₀] using hb
  · simpa only [← hP, hb, ← hp₀] using hclose
  · have h := W.support
    rw [← hlist, hps, ← hp₀] at h
    exact h
  · have h := W.edges
    change W.cycle.edges = s(W.base, (W.pieces (pChildIndex F A u hbase)).finish) ::
      (chainEdges p₀ ps).reverse at h
    rw [← hfinish, hps, ← hp₀] at h
    exact h

/-- Eight actual paths with the literal third-order orientations form
the joint partition of this same saved parent cycle. -/
theorem native_j2_same_parent_eight_piece_partition {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    let N₀ := nextFrame (reverseSelected F) A u hbase
    let N₁ := nextFrame F A u hbase
    ∃ (joint : Fin 8 → Piece (ParentGraph F A u hbase))
      (K H : Finset (Sym2 (ParentVertex F A u hbase))),
      Disjoint K H ∧
      K.image (Sym2.map Subtype.val) = markedCuts N₀ ∧
      H.image (Sym2.map Subtype.val) = markedCuts N₁ ∧
      ActualCyclePartition W.cycle (K ∪ H) (List.ofFn joint) ∧
      ∀ i : Fin 8,
        (joint i).start.val = ![leftPort N₀ 0, rightPort N₀ 0, rightPort N₁ 0,
          rightPort N₀ 1, leftPort N₁ 3, rightPort N₁ 2,
          rightPort N₁ 1, leftPort N₁ 2] i ∧
        (joint i).finish.val = ![leftPort N₀ 2, leftPort N₁ 0, leftPort N₁ 1,
          rightPort N₀ 2, rightPort N₀ 3, leftPort N₀ 3,
          rightPort N₁ 3, leftPort N₀ 1] i := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let B := reverseSelected F
  let N₀ := nextFrame B A u hbase
  let N₁ := nextFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let lift := rawPParentMap F A u hbase hA
  let old (i : Fin 6) := mapPiece lift (W.P.seed.joint i)
  let rest := [old 0, old 2, old 3, old 4, old 5]
  let deleted := (W.P.seed.H.toList ++ W.P.seed.K.toList).map (Sym2.map lift)
  obtain ⟨s, t, hs, ht, hₐ, h_b, tail, hd, P, hP, hPs, hPe⟩ :=
    same_p_parent_opening hm F A u hbase hA W
  obtain ⟨r₀, ℓ₀, r₁, ℓ₁, hr₀, hℓ₀, hr₁, hℓ₁,
      q₀, q₁, q₂, _, _, _, hQs, hQe, _⟩ :=
    native_j2_same_q_three_fragments hm F A u hbase hA W
  let qLift := childLift O ⟨0, by
    have hlen := outer_base_bound F A u hbase hA
    change 0 < (outerFrame F A u hbase).base.length
    omega⟩
  let Λ := W.special.path.map qLift
  let q : Piece (ParentGraph F A u hbase) := ⟨_, _, Λ⟩
  have hq : q = W.pieces ⟨0, by
      simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩ := by
    rw [W.childPieces]
    dsimp only [parentPiece]
    rw [W.specialPath]
    rfl
  obtain ⟨others, hlink, hb, hclose, hcs, hce⟩ :=
    same_parent_chain_inventory hm F A u hbase hA W q ⟨s, t, P⟩ hq hP
  have hQs' : (q₀.map qLift).support ++ (q₁.map qLift).support ++
      (q₂.map qLift).support = Λ.support := by
    simpa only [Λ, SimpleGraph.Walk.support_map, List.map_append] using
      congrArg (List.map qLift) hQs
  have hQe' : (q₀.map qLift).edges ++ [s(qLift ℓ₀, qLift r₀)] ++
      (q₁.map qLift).edges ++ [s(qLift ℓ₁, qLift r₁)] ++ (q₂.map qLift).edges =
      Λ.edges := by
    simpa only [Λ, SimpleGraph.Walk.edges_map, List.map_append, List.map_cons,
      List.map_nil, Sym2.map_mk] using congrArg (List.map (Sym2.map qLift)) hQe
  obtain ⟨hKold, hHold⟩ := same_seed_marked_cut_images hm F W.P
  have hdeleted : (deleted.map (Sym2.map Subtype.val)).toFinset =
      markedCuts F ∪ markedCuts B := by
    simp only [deleted, List.map_map, Function.comp_def, Sym2.map_map]
    change ((W.P.seed.H.toList ++ W.P.seed.K.toList).map
      (Sym2.map Subtype.val)).toFinset = _
    have hmap (S : Finset (Sym2 {x : Configuration m // FrameDomain F x})) :
        (S.toList.map (Sym2.map Subtype.val)).toFinset =
          S.image (Sym2.map Subtype.val) := by
      ext e
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_toList, Finset.mem_image]
    rw [List.map_append, List.toFinset_append, hmap, hmap, hHold, hKold, Finset.union_comm]
  have holdDisjoint : Disjoint (markedCuts F) (markedCuts B) := by
    rw [← hKold, ← hHold]
    apply Finset.disjoint_left.mpr
    intro e heK heH
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heK
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heH
    have hxy := (Sym2.map.injective Subtype.val_injective) (hxe.trans hye.symm)
    exact Finset.disjoint_left.mp W.P.seed.partitions.disjoint hx (hxy.symm ▸ hy)
  have holdPorts := same_old_joint_native_ports hm F A u hbase hA W
  have hℓ : (old 1).start.val = leftPort F 0 := (holdPorts 1).1
  have hz : (old 1).finish.val = leftPort B 1 := (holdPorts 1).2
  obtain ⟨new₀, new₁, new₂, _, _, _, _, _, _, _, _, _,
      K, H, hKH, hK, hH, _, _, _, _, _, hsupport, hedges, hcuts⟩ :=
    native_actual_closed_parent_joint_update (by omega : 3 ≤ m) (by omega : 2 ≤ 2)
      F B A u hbase hbase true W.cycle W.hamiltonian
      (old 1).walk tail hₐ h_b hd rest P deleted hPs hPe hdeleted holdDisjoint
      Λ (q₀.map qLift) (q₁.map qLift) (q₂.map qLift) hQs' hQe'
      others hlink hb hclose hcs hce hℓ hz hℓ₀ hr₀ hℓ₁ hr₁
  let joint : Fin 8 → Piece (ParentGraph F A u hbase) :=
    ![⟨qLift ℓ₀, (old 1).finish, new₀.reverse⟩,
      ⟨qLift r₀, qLift ℓ₁, new₁⟩,
      ⟨qLift r₁, (old 1).start, new₂⟩,
      old 4, old 3, old 2, old 0, old 5]
  let changed : List (Piece (ParentGraph F A u hbase)) :=
    [⟨(old 1).finish, qLift ℓ₀, new₀⟩, ⟨qLift r₀, qLift ℓ₁, new₁⟩,
      ⟨qLift r₁, (old 1).start, new₂⟩] ++ rest
  have hsperm : ((List.ofFn joint).flatMap fun p => p.walk.support).Perm
      (changed.flatMap fun p => p.walk.support) := by
    apply List.perm_iff_count.mpr
    intro x
    simp only [joint, changed, rest, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
      List.count_append, List.count_reverse, List.count_nil, SimpleGraph.Walk.support_reverse]
    omega
  have heperm : ((List.ofFn joint).flatMap fun p => p.walk.edges).Perm
      (changed.flatMap fun p => p.walk.edges) := by
    apply List.perm_iff_count.mpr
    intro e
    simp only [joint, changed, rest, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
      List.count_append, List.count_reverse, List.count_nil, SimpleGraph.Walk.edges_reverse]
    omega
  refine ⟨joint, K, H, hKH, hK, hH,
    ⟨hsperm.trans hsupport, heperm.trans hedges, hcuts⟩, ?_⟩
  intro i
  have hshift (j : ℕ) := native_marked_index_shift (by omega : 3 ≤ m) F A u hbase j
  have hbarshift (j : ℕ) := native_marked_index_shift (by omega : 3 ≤ m) B A u hbase j
  fin_cases i
  · exact ⟨hℓ₀, hz.trans (hbarshift 1).2.symm⟩
  · exact ⟨hr₀, hℓ₁⟩
  · exact ⟨hr₁, hℓ.trans (hshift 0).2.symm⟩
  · exact ⟨(holdPorts 4).1.trans (hbarshift 0).1.symm,
      (holdPorts 4).2.trans (hbarshift 1).1.symm⟩
  · exact ⟨(holdPorts 3).1.trans (hshift 2).2.symm,
      (holdPorts 3).2.trans (hbarshift 2).1.symm⟩
  · exact ⟨(holdPorts 2).1.trans (hshift 1).1.symm,
      (holdPorts 2).2.trans (hbarshift 2).2.symm⟩
  · exact ⟨(holdPorts 0).1.trans (hshift 0).1.symm,
      (holdPorts 0).2.trans (hshift 2).1.symm⟩
  · exact ⟨(holdPorts 5).1.trans (hshift 1).2.symm,
      (holdPorts 5).2.trans (hbarshift 0).2.symm⟩

#print axioms native_j2_same_parent_eight_piece_partition

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2JointPromotion
