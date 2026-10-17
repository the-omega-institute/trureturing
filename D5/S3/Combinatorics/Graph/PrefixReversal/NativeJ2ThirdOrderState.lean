/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same actual J2 parent initializes the full native third-order induction state. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentRetention
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2JointPromotion
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeThirdOrderBoundaryBase
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeMarkedPorts
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFramePredecessor

set_option autoImplicit false
-- The transported frame base proofs use definitional identities across selected-order exchange.
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ThirdOrderState

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeMarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentRetention
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2JointPromotion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2FrameTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeFramePredecessor
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeThirdOrderBoundaryBase
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open private R L cut cuts from
  D5.S3.Combinatorics.Graph.Walks.ActualThirdOrderBoundaryBase
open private swap_selected_perm from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders

private def jointPorts {V : Type*} {G : SimpleGraph V} (joint : Fin 8 → Piece G)
    (p : Bool × Fin 4 × Bool) : V :=
  if p.1 then
    if p.2.2 then ![(joint 1).finish, (joint 2).finish, (joint 7).start, (joint 4).start] p.2.1
    else ![(joint 2).start, (joint 6).start, (joint 5).start, (joint 6).finish] p.2.1
  else
    if p.2.2 then ![(joint 0).start, (joint 7).finish, (joint 0).finish, (joint 5).finish] p.2.1
    else ![(joint 1).start, (joint 3).start, (joint 3).finish, (joint 4).finish] p.2.1

private theorem state_from_eight_paths {m : ℕ} (F : SupplyFrame m 3)
    (hB : 3 ≤ F.base.length)
    {base : {x : Configuration m // SpecialDomain F hB x}}
    (w : (domainGraph (SpecialDomain F hB)).Walk base base) (hw : w.IsHamiltonianCycle)
    (joint : Fin 8 → Piece (domainGraph (SpecialDomain F hB)))
    (K H : Finset (Sym2 {x : Configuration m // SpecialDomain F hB x}))
    (hK : K.image (Sym2.map Subtype.val) = markedCuts F)
    (hH : H.image (Sym2.map Subtype.val) = markedCuts (oppositeSelectedFrame F (by omega)))
    (hj : ActualCyclePartition w (K ∪ H) (List.ofFn joint))
    (hends : ∀ i : Fin 8,
      (joint i).start.val = ![leftPort F 0, rightPort F 0,
        rightPort (oppositeSelectedFrame F (by omega)) 0, rightPort F 1,
        leftPort (oppositeSelectedFrame F (by omega)) 3,
        rightPort (oppositeSelectedFrame F (by omega)) 2,
        rightPort (oppositeSelectedFrame F (by omega)) 1,
        leftPort (oppositeSelectedFrame F (by omega)) 2] i ∧
      (joint i).finish.val = ![leftPort F 2,
        leftPort (oppositeSelectedFrame F (by omega)) 0,
        leftPort (oppositeSelectedFrame F (by omega)) 1,
        rightPort F 2, rightPort F 3, leftPort F 3,
        rightPort (oppositeSelectedFrame F (by omega)) 3, leftPort F 1] i)
    (hkeepA : ∀ (x y : {z : Configuration m // SpecialDomain F hB z}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠
        s(protectedP F (by omega), protectedQ F (by omega)) → s(x, y) ∈ w.edges)
    (hkeepB : ∀ (x y : {z : Configuration m // SpecialDomain F hB z}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ F.selected.toFinset → s(x, y) ∈ w.edges)
    (hC : ∀ x : Configuration m, s(x, x * c m) ∈ w.edges.map (Sym2.map Subtype.val) →
      x (Fin.last m) ∈ F.selected.toFinset) :
    ∃ S : StateFor F (by omega) hB, S.base = base ∧ HEq S.walk w ∧
      S.primaryOdd = true ∧ S.oppositeOdd = false ∧ S.distinguishedOpposite = false := by
  classical
  let B := oppositeSelectedFrame F (by omega)
  let p := jointPorts joint
  have hports : ∀ (t : Bool) (i : Fin 4),
      (R p t i).val = rightPort (if t then B else F) i.val ∧
      (L p t i).val = leftPort (if t then B else F) i.val := by
    intro t i
    cases t <;> fin_cases i <;> constructor
    all_goals first
      | exact (hends 0).1 | exact (hends 0).2
      | exact (hends 1).1 | exact (hends 1).2
      | exact (hends 2).1 | exact (hends 2).2
      | exact (hends 3).1 | exact (hends 3).2
      | exact (hends 4).1 | exact (hends 4).2
      | exact (hends 5).1 | exact (hends 5).2
      | exact (hends 6).1 | exact (hends 6).2
      | exact (hends 7).1 | exact (hends 7).2
  have hraw (q : Bool × Fin 4 × Bool) :
      (p q).val = specialPort (if q.1 then B else F)
        (q.2.1, if q.2.2 then 1 else 0) := by
    rcases q with ⟨t, i, side⟩
    cases side
    · simpa only [specialPort, Bool.false_eq_true, ↓reduceIte, Fin.val_zero] using (hports t i).1
    · simpa only [specialPort, ↓reduceIte, Fin.val_one, one_ne_zero] using (hports t i).2
  have hp : Function.Injective p := by
    intro q r he
    have hr := congrArg Subtype.val he
    rw [hraw q, hraw r] at hr
    have hi : (q.1, (q.2.1, if q.2.2 then (1 : Fin 2) else 0)) =
        (r.1, (r.2.1, if r.2.2 then (1 : Fin 2) else 0)) :=
      native_opposite_marked_port_injective F (by omega) hB (by simpa only [B] using hr)
    have ht := congrArg Prod.fst hi
    have hidx := congrArg (fun z : Bool × (Fin 4 × Fin 2) => z.2.1) hi
    have hs := congrArg (fun z : Bool × (Fin 4 × Fin 2) => z.2.2) hi
    have hside : q.2.2 = r.2.2 := by
      cases hq : q.2.2 <;> cases hr : r.2.2 <;> simp_all
    exact Prod.ext ht (Prod.ext hidx hside)
  have hcuts (t : Bool) : (cuts p t).image (Sym2.map Subtype.val) =
      markedCuts (if t then B else F) := by
    simp only [cuts, Finset.image_image, markedCuts]
    apply congrArg (fun z : Fin 4 → Sym2 (Configuration m) => Finset.univ.image z)
    funext i
    change s((R p t i).val, (L p t i).val) =
      s(rightPort (if t then B else F) i.val, leftPort (if t then B else F) i.val)
    rw [(hports t i).1, (hports t i).2]
  have hKeq : K = cuts p false :=
    Finset.image_injective (Sym2.map.injective Subtype.val_injective)
      (hK.trans (hcuts false).symm)
  have hHeq : H = cuts p true :=
    Finset.image_injective (Sym2.map.injective Subtype.val_injective)
      (hH.trans (hcuts true).symm)
  rw [hKeq, hHeq] at hj
  let d : (domainGraph (SpecialDomain F hB)).Walk (L p false 0) (L p false 2) := (joint 0).walk
  let cross : (domainGraph (SpecialDomain F hB)).Walk (R p false 0) (L p true 0) := (joint 1).walk
  let g : (domainGraph (SpecialDomain F hB)).Walk (R p true 0) (L p true 1) := (joint 2).walk
  let a₀ : (domainGraph (SpecialDomain F hB)).Walk (R p false 1) (R p false 2) := (joint 3).walk
  let b₀ : (domainGraph (SpecialDomain F hB)).Walk (L p true 3) (R p false 3) := (joint 4).walk
  let q : (domainGraph (SpecialDomain F hB)).Walk (R p true 2) (L p false 3) := (joint 5).walk
  let e : (domainGraph (SpecialDomain F hB)).Walk (R p true 1) (R p true 3) := (joint 6).walk
  let f : (domainGraph (SpecialDomain F hB)).Walk (L p true 2) (L p false 1) := (joint 7).walk
  have hj' : ActualCyclePartition w (cuts p false ∪ cuts p true)
      [⟨_, _, d⟩, ⟨_, _, cross⟩, ⟨_, _, g⟩, ⟨_, _, a₀⟩,
        ⟨_, _, b₀⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩] := by
    change ActualCyclePartition w (cuts p false ∪ cuts p true) (List.ofFn joint)
    exact hj
  obtain ⟨p₁, p₂, o₀, o₂, hs, hp₀, hp₁, hcut₀, hcut₁, _⟩ :=
    native_third_order_boundary_base F B Subtype.val p hp hports w hw
      d cross g a₀ b₀ q e f hj'
  let S : StateFor F (by omega) hB := {
    oppositeFrame := B
    canonicalOpposite := rfl
    sameSelected := List.toFinset_eq_of_perm _ _ (swap_selected_perm F (by omega))
    sameBase := rfl
    sameTerminal := rfl
    sameProtectedPair := by
      rw [(native_opposite_protected_labels F (by omega)).1,
        (native_opposite_protected_labels F (by omega)).2, Sym2.eq_swap]
    primaryOdd := true
    oppositeOdd := false
    distinguishedOpposite := false
    base := base
    walk := w
    hamiltonian := hw
    K := cuts p false
    H := cuts p true
    primaryCuts := hcut₀
    oppositeCuts := hcut₁
    left := L p false 0
    right := R p false 0
    otherLeft := L p true 0
    far := L p false 2
    primaryFar := L p false 2
    oppositeFar := L p true 2
    leftCoordinate := (hports false 0).2
    rightCoordinate := (hports false 0).1
    otherLeftCoordinate := (hports true 0).2
    farCoordinate := (hports false 2).2
    primaryFarCoordinate := (hports false 2).2
    oppositeFarCoordinate := (hports true 2).2
    distinguished := d
    crossing := cross
    jointRest := [⟨_, _, g⟩, ⟨_, _, a₀⟩, ⟨_, _, b₀⟩, ⟨_, _, q⟩, ⟨_, _, e⟩, ⟨_, _, f⟩]
    primary := d
    primaryRest := [⟨_, _, a₀⟩, ⟨_, _, p₁⟩, ⟨_, _, p₂⟩]
    opposite := o₀
    oppositeRest := [⟨_, _, g⟩, ⟨_, _, e⟩, ⟨_, _, o₂⟩]
    partitions := hs
    primaryBoundary := hp₀
    oppositeBoundary := hp₁
    firstCut := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    keepsProtectedA := hkeepA
    keepsRemainingB := hkeepB
    selectedC := hC }
  exact ⟨S, rfl, HEq.rfl, rfl, rfl, rfl⟩


/-- The actual eight-piece partition and the earned retained edges of
this same outer parent initialize every field of the strong k3 state. -/
theorem native_j2_parent_third_order_state {m : ℕ} (hm : 5 ≤ m)
    (F : SupplyFrame m 2) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterParentWitnessFor hm F A u hbase hA) :
    ∃ S : StateFor (nextFrame (reverseSelected F) A u hbase) (by omega)
        (by simpa only [nextFrame] using hA),
      S.primaryOdd = true ∧ S.oppositeOdd = false ∧ S.distinguishedOpposite = false := by
  classical
  let B := reverseSelected F
  let N := nextFrame B A u hbase
  let P := nextFrame F A u hbase
  have hN : 3 ≤ N.base.length := by simpa only [N, nextFrame] using hA
  have hsel : F.selected.toFinset = B.selected.toFinset := by simp [B, reverseSelected]
  let middle := parentOrderDomainMap F B A u hbase hbase hsel rfl
  let lift := (parentNextMarkedMap B A u hbase hA).comp middle
  have hbij : Function.Bijective lift :=
    (parent_next_marked_map_bijective B A u hbase hA).comp
      (parent_order_domain_map_bijective F B A u hbase hbase hsel rfl)
  have hval : ∀ x, (lift x).val = x.val := fun _ => rfl
  have hBopp : oppositeSelectedFrame B (by omega) = F := by
    change oppositeSelectedFrame (reverseSelected F) (by omega) = F
    rw [← native_opposite_selected_two F]
    exact native_opposite_selected_involutive F (by omega)
  have hcan : oppositeSelectedFrame N (by omega) = P := by
    change oppositeSelectedFrame (nextFrame B A u hbase) (by omega) = _
    rw [native_opposite_next_frame B (by omega) A u hbase]
    simpa only [hBopp, P]
  have hpair : s(protectedP N (by omega), protectedQ N (by omega)) =
      s(protectedP F (by omega), protectedQ F (by omega)) := by
    have hnp := native_protected_labels_prepend B N (by omega) u rfl
    rw [hnp.1, hnp.2]
    change s(protectedP (reverseSelected F) (by omega),
      protectedQ (reverseSelected F) (by omega)) = _
    rw [← native_opposite_selected_two F,
      (native_opposite_protected_labels F (by omega)).1,
      (native_opposite_protected_labels F (by omega)).2, Sym2.eq_swap]
  have hselected : N.selected.toFinset = insert u F.selected.toFinset := by
    simp [N, nextFrame, B, reverseSelected]
  obtain ⟨joint, K, H, _, hK, hH, hj, hends⟩ :=
    native_j2_same_parent_eight_piece_partition hm F A u hbase hA W
  let mapped : Fin 8 → Piece (domainGraph (SpecialDomain N hN)) := fun i => mapPiece lift (joint i)
  let K' := K.image (Sym2.map lift)
  let H' := H.image (Sym2.map lift)
  let w := W.cycle.map lift
  have hw : w.IsHamiltonianCycle := SimpleGraph.Walk.IsHamiltonianCycle.map hbij W.hamiltonian
  have rawmap : Sym2.map Subtype.val ∘ Sym2.map lift =
      (Sym2.map Subtype.val : Sym2 _ → Sym2 (Configuration m)) := by
    funext e
    rw [Function.comp_apply, Sym2.map_map]
    rfl
  have hK' : K'.image (Sym2.map Subtype.val) = markedCuts N := by
    dsimp only [K']
    rw [Finset.image_image, rawmap]
    exact hK
  have hH' : H'.image (Sym2.map Subtype.val) = markedCuts (oppositeSelectedFrame N (by omega)) := by
    dsimp only [H']
    rw [Finset.image_image, rawmap, hcan]
    exact hH
  have hmapped : (List.ofFn joint).map (mapPiece lift) = List.ofFn mapped := by
    rw [List.map_ofFn]
    rfl
  obtain ⟨_, _, hs, he, hc⟩ := actual_cycle_partition_map lift hbij.injective
    W.cycle W.hamiltonian.isCycle (List.ofFn joint) (K ∪ H)
    hj.support hj.edges hj.cut_mem
  have hj' : ActualCyclePartition w (K' ∪ H') (List.ofFn mapped) := by
    rw [hmapped] at hs he
    rw [Finset.image_union] at he hc
    exact ⟨hs, he, hc⟩
  have hends' : ∀ i : Fin 8,
      (mapped i).start.val = ![leftPort N 0, rightPort N 0,
        rightPort (oppositeSelectedFrame N (by omega)) 0, rightPort N 1,
        leftPort (oppositeSelectedFrame N (by omega)) 3,
        rightPort (oppositeSelectedFrame N (by omega)) 2,
        rightPort (oppositeSelectedFrame N (by omega)) 1,
        leftPort (oppositeSelectedFrame N (by omega)) 2] i ∧
      (mapped i).finish.val = ![leftPort N 2,
        leftPort (oppositeSelectedFrame N (by omega)) 0,
        leftPort (oppositeSelectedFrame N (by omega)) 1,
        rightPort N 2, rightPort N 3, leftPort N 3,
        rightPort (oppositeSelectedFrame N (by omega)) 3, leftPort N 1] i := by
    intro i
    simpa only [mapped, mapPiece, hval, hcan] using hends i
  obtain ⟨hAkeep, hBkeep, hCkeep⟩ := native_j2_outer_parent_retention hm F A u hbase hA W
  have hA' : ∀ (x y : {z : Configuration m // SpecialDomain N hN z}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠
        s(protectedP N (by omega), protectedQ N (by omega)) → s(x, y) ∈ w.edges := by
    intro x y hy hp
    obtain ⟨x', rfl⟩ := hbij.surjective x
    obtain ⟨y', rfl⟩ := hbij.surjective y
    rw [hval, hval] at hy hp
    rw [hpair] at hp
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), hAkeep x' y' hy hp, rfl⟩
  have hB' : ∀ (x y : {z : Configuration m // SpecialDomain N hN z}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ N.selected.toFinset → s(x, y) ∈ w.edges := by
    intro x y hy ht
    obtain ⟨x', rfl⟩ := hbij.surjective x
    obtain ⟨y', rfl⟩ := hbij.surjective y
    rw [hval, hval] at hy
    rw [hval, hselected] at ht
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), hBkeep x' y' hy ht, rfl⟩
  have hC' : ∀ x : Configuration m, s(x, x * c m) ∈ w.edges.map (Sym2.map Subtype.val) →
      x (Fin.last m) ∈ N.selected.toFinset := by
    intro x hx
    change s(x, x * c m) ∈ (W.cycle.map lift).edges.map (Sym2.map Subtype.val) at hx
    rw [SimpleGraph.Walk.edges_map, List.map_map, rawmap] at hx
    rw [hselected]
    exact hCkeep x hx
  obtain ⟨S, _, _, hprimary, hopposite, hdistinguished⟩ :=
    state_from_eight_paths N hN w hw mapped K' H' hK' hH' hj' hends' hA' hB' hC'
  exact ⟨S, hprimary, hopposite, hdistinguished⟩

/-- Every literal three-selected-label frame has a full strong actual
state. A predecessor supplies its own native P/Q witnesses; the double
protected-label exchange returns the originally supplied frame. -/
theorem native_third_order_state_exists {m : ℕ} (F : SupplyFrame m 3)
    (hB : 3 ≤ F.base.length) :
    ∃ S : StateFor F (by omega) hB,
      S.primaryOdd = true ∧ S.oppositeOdd = false ∧ S.distinguishedOpposite = false := by
  have hp := F.prefix_length
  simp only [List.length_append, F.selected_length] at hp
  have hm : 5 ≤ m := by omega
  obtain ⟨P, u, hbase, hnext, _, _, _, _⟩ := native_frame_predecessor F
  obtain ⟨W⟩ := native_j2_outer_parent_with_raw_p_q hm (reverseSelected P)
    F.base u hbase hB
  have h := native_j2_parent_third_order_state hm (reverseSelected P) F.base u hbase hB W
  have hframe : nextFrame (reverseSelected (reverseSelected P)) F.base u hbase = F := by
    calc
      _ = nextFrame P F.base u hbase := by
        cases P
        simp only [reverseSelected, nextFrame, List.reverse_reverse]
      _ = F := hnext
  have transport (N : SupplyFrame m 3) (hNF : N = F) (hN : 3 ≤ N.base.length)
      (hh : ∃ S : StateFor N (by omega) hN,
        S.primaryOdd = true ∧ S.oppositeOdd = false ∧ S.distinguishedOpposite = false) :
      ∃ S : StateFor F (by omega) hB,
        S.primaryOdd = true ∧ S.oppositeOdd = false ∧ S.distinguishedOpposite = false := by
    subst N
    exact hh
  exact transport _ hframe _ h

#print axioms native_j2_parent_third_order_state
#print axioms native_third_order_state_exists

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ThirdOrderState
