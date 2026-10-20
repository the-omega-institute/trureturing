/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Earn both new cut inventories on the same actual parent. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateQPromotion
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate

set_option autoImplicit false
-- The saved child-domain identities unfold across the dependent frame maps.
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateJointPromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualJointUpdate
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
open private original_state_p_joint_split same_parent_chain from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStatePromotion
open private same_state_q_three_fragments from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateQPromotion
open private pChildIndex old_base_bound outer_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private childLift parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private special_child_path from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep

private theorem piece_copy_eq {V : Type*} {G : SimpleGraph V}
    (p : Piece G) (a b : V) (ha : p.start = a) (hb : p.finish = b) :
    (⟨a, b, p.walk.copy ha hb⟩ : Piece G) = p := by
  rcases p with ⟨x, y, w⟩
  dsimp only at ha hb
  subst a
  subst b
  rfl

/-- The literal P opening used in W has the transported split and exact
inventories of the original retained P seed. No new P path is selected. -/
private theorem same_p_parent_opening {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA) :
    let O := outerFrame F A u hbase
    let lift := pMarkedParentLift F A u hbase hA
    let d := W.P.distinguished.map lift
    let rest := (⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest).map (mapPiece lift)
    let deleted := (W.P.H.toList ++ W.P.K.toList).map (Sym2.map lift)
    ∃ s t : ParentVertex F A u hbase,
      s.val = rightPort O (m - 1) ∧ t.val = leftPort O (m - 1) ∧
      ∃ (hₐ : (ParentGraph F A u hbase).Adj (lift W.P.left) s)
        (h_b : (ParentGraph F A u hbase).Adj s t)
        (tail : (ParentGraph F A u hbase).Walk t (lift W.P.far)),
        d = (tail.cons h_b).cons hₐ ∧
        ∃ P : (ParentGraph F A u hbase).Walk s t,
          (⟨s, t, P⟩ : Piece (ParentGraph F A u hbase)) =
            W.pieces (pChildIndex F A u hbase) ∧
          P.support.Perm (d.support ++ rest.flatMap fun p => p.walk.support) ∧
          P.edges.Perm ((rest.flatMap fun p => p.walk.edges) ++
            tail.edges ++ [s(lift W.P.left, s)] ++ deleted) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let j := pChildIndex F A u hbase
  let lift := pMarkedParentLift F A u hbase hA
  obtain ⟨s₀, t₀, hs₀, ht₀, hₐ, h_b, tail, hd, _, hPs, hPe⟩ :=
    original_state_p_joint_split hm hk F A u hbase hA W
  have hidx : k + j.val = m - 1 := by
    have h := F.prefix_length
    rw [hbase, List.length_append, F.selected_length,
      List.length_append, List.length_singleton] at h
    change k + A.length = m - 1
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
    simpa only [parentPiece, childLift, lift, pMarkedParentLift, RelHom.coeFn_mk, j,
      SimpleGraph.Walk.support_map, List.flatMap_map, mapPiece,
      List.map_append, List.map_map, List.map_flatMap, Function.comp_def,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
      using hPs
  · apply (List.map_perm_map_iff (Sym2.map.injective Subtype.val_injective)).mp
    dsimp only [P]
    rw [SimpleGraph.Walk.edges_copy, W.childPieces j]
    simpa only [parentPiece, childLift, lift, pMarkedParentLift, RelHom.coeFn_mk, j,
      SimpleGraph.Walk.edges_map, List.flatMap_map, mapPiece,
      List.map_append, List.map_map, List.map_flatMap, List.map_cons, List.map_nil,
      Sym2.map_map, Sym2.map_mk, Function.comp_def, List.append_assoc,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
      using hPe

/-- Retain the literal saved first and last openings while exposing the
intervening list required by the closed-parent joint constructor. -/
private theorem same_parent_chain_inventory {m k : ℕ} (hm : 3 ≤ m) (hk : 2 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA)
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
  obtain ⟨hb, hlink, hfinish, hclose⟩ := same_parent_chain hm hk F A u hbase hA W
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


structure CurrentJointFor {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F (by omega) A u hbase hA) where
  r₀ : ParentVertex F A u hbase
  ℓ₀ : ParentVertex F A u hbase
  r₁ : ParentVertex F A u hbase
  ℓ₁ : ParentVertex F A u hbase
  right₀ : r₀.val = rightPort (nextFrame (oppositeSelectedFrame F (by omega)) A u hbase) 0
  left₀ : ℓ₀.val = leftPort (nextFrame (oppositeSelectedFrame F (by omega)) A u hbase) 0
  right₁ : r₁.val = rightPort (nextFrame F A u hbase) 0
  left₁ : ℓ₁.val = leftPort (nextFrame F A u hbase) 0
  new₀ : (ParentGraph F A u hbase).Walk ((pMarkedParentLift F A u hbase hA) W.P.far) ℓ₀
  new₁ : (ParentGraph F A u hbase).Walk r₀ ℓ₁
  new₂ : (ParentGraph F A u hbase).Walk r₁ ((pMarkedParentLift F A u hbase hA) W.P.left)
  K : Finset (Sym2 (ParentVertex F A u hbase))
  H : Finset (Sym2 (ParentVertex F A u hbase))
  disjoint : Disjoint K H
  primaryCuts : K.image (Sym2.map Subtype.val) =
    markedCuts (nextFrame (oppositeSelectedFrame F (by omega)) A u hbase)
  oppositeCuts : H.image (Sym2.map Subtype.val) = markedCuts (nextFrame F A u hbase)
  zero₀ : s(ℓ₀, r₀) ∈ K
  zero₁ : s(ℓ₁, r₁) ∈ H
  erase₀ : K.erase s(ℓ₀, r₀) = W.P.H.image (Sym2.map (pMarkedParentLift F A u hbase hA))
  erase₁ : H.erase s(ℓ₁, r₁) = W.P.K.image (Sym2.map (pMarkedParentLift F A u hbase hA))
  partition : ActualCyclePartition W.cycle (K ∪ H)
    ([⟨(pMarkedParentLift F A u hbase hA) W.P.far, ℓ₀, new₀⟩,
      ⟨r₀, ℓ₁, new₁⟩, ⟨r₁, (pMarkedParentLift F A u hbase hA) W.P.left, new₂⟩] ++
      ((⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest).map
        (mapPiece (pMarkedParentLift F A u hbase hA))))

private theorem current_joint_from_same_state_parent {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F (by omega) A u hbase hA) :
    Nonempty (CurrentJointFor hm hk F A u hbase hA W) := by
  classical
  let O := outerFrame F A u hbase
  let B := oppositeSelectedFrame F (by omega)
  let hBO := outer_base_bound F A u hbase hA
  let lift := pMarkedParentLift F A u hbase hA
  let d := W.P.distinguished.map lift
  let rest := (⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest).map (mapPiece lift)
  let deleted := (W.P.H.toList ++ W.P.K.toList).map (Sym2.map lift)
  obtain ⟨s, t, hs, ht, hₐ, h_b, tail, hd, P, hP, hPs, hPe⟩ :=
    same_p_parent_opening hm (by omega) F A u hbase hA W
  obtain ⟨r₀, ℓ₀, r₁, ℓ₁, hr₀, hℓ₀, hr₁, hℓ₁,
      q₀, q₁, q₂, _, _, _, hQs, hQe, _⟩ :=
    same_state_q_three_fragments hm hk F A u hbase hA W
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
    same_parent_chain_inventory hm (by omega) F A u hbase hA W q ⟨s, t, P⟩ hq hP
  have hQs' : (q₀.map qLift).support ++ (q₁.map qLift).support ++
      (q₂.map qLift).support = Λ.support := by
    simpa only [Λ, SimpleGraph.Walk.support_map, List.map_append] using
      congrArg (List.map qLift) hQs
  have hQe' : (q₀.map qLift).edges ++ [s(qLift ℓ₀, qLift r₀)] ++
      (q₁.map qLift).edges ++ [s(qLift ℓ₁, qLift r₁)] ++ (q₂.map qLift).edges = Λ.edges := by
    simpa only [Λ, SimpleGraph.Walk.edges_map, List.map_append, List.map_cons,
      List.map_nil, Sym2.map_mk] using congrArg (List.map (Sym2.map qLift)) hQe
  have hKold : W.P.K.image (Sym2.map Subtype.val) = markedCuts F := W.P.primaryCuts
  have hHold : W.P.H.image (Sym2.map Subtype.val) = markedCuts B := by
    rw [W.P.oppositeCuts, W.P.canonicalOpposite]
  have hdeleted : (deleted.map (Sym2.map Subtype.val)).toFinset =
      markedCuts F ∪ markedCuts B := by
    simp only [deleted, List.map_map, Function.comp_def, Sym2.map_map]
    change ((W.P.H.toList ++ W.P.K.toList).map (Sym2.map Subtype.val)).toFinset = _
    have hmap (S : Finset (Sym2 {x : Configuration m //
        SpecialDomain F (old_base_bound F A u hbase hA) x})) :
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
    exact Finset.disjoint_left.mp W.P.partitions.disjoint hx (hxy.symm ▸ hy)
  have hℓ : (lift W.P.left).val = leftPort F 0 := W.P.leftCoordinate
  have hz : (lift W.P.far).val =
      leftPort (if W.P.distinguishedOpposite then B else F) (k - 1) := by
    simpa only [lift, pMarkedParentLift, RelHom.coeFn_mk, B, W.P.canonicalOpposite] using W.P.farCoordinate
  obtain ⟨new₀, new₁, new₂, _, _, _, _, _, _, _, _, _,
      K, H, hKH, hK, hH, _, hzero₀, hzero₁, herase₀, herase₁, hsupport, hedges, hcuts⟩ :=
    native_actual_closed_parent_joint_update hm (by omega) F B A u hbase hbase
      W.P.distinguishedOpposite W.cycle W.hamiltonian d tail hₐ h_b hd rest P deleted
      hPs hPe hdeleted holdDisjoint
      Λ (q₀.map qLift) (q₁.map qLift) (q₂.map qLift) hQs' hQe'
      others hlink hb hclose hcs hce hℓ hz hℓ₀ hr₀ hℓ₁ hr₁
  have he₀ : K.erase s(qLift ℓ₀, qLift r₀) = W.P.H.image (Sym2.map lift) := by
    apply Finset.image_injective (Sym2.map.injective Subtype.val_injective)
    rw [herase₀]
    simpa only [Finset.image_image, Function.comp_def, Sym2.map_map, lift, pMarkedParentLift, RelHom.coeFn_mk] using hHold.symm
  have he₁ : H.erase s(qLift ℓ₁, qLift r₁) = W.P.K.image (Sym2.map lift) := by
    apply Finset.image_injective (Sym2.map.injective Subtype.val_injective)
    rw [herase₁]
    simpa only [Finset.image_image, Function.comp_def, Sym2.map_map, lift, pMarkedParentLift, RelHom.coeFn_mk] using hKold.symm
  exact ⟨⟨qLift r₀, qLift ℓ₀, qLift r₁, qLift ℓ₁, hr₀, hℓ₀, hr₁, hℓ₁,
    new₀, new₁, new₂, K, H, hKH, hK, hH, hzero₀, hzero₁, he₀, he₁,
    ⟨hsupport, hedges, hcuts⟩⟩⟩

#print axioms current_joint_from_same_state_parent

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateJointPromotion
