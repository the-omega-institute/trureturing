/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Advance both actual orders and retained-edge invariants on one cycle. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateJointPromotion
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeFullStateTransport

set_option autoImplicit false
-- The saved child-domain identities unfold across the dependent frame maps.
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStrongStateStep

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeFullStateTransport
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualPartitionTransport
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
open private state_parent_retention from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateJointPromotion
open private old_base_bound outer_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses

private theorem strong_state_from_same_parent {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F (by omega) A u hbase hA)
    (J : CurrentJointFor hm hk F A u hbase hA W) :
    ∃ S : StateFor (nextFrame (oppositeSelectedFrame F (by omega)) A u hbase)
        (by omega) (by simpa only [nextFrame] using hA),
      S.primaryOdd = W.P.oppositeOdd ∧ S.oppositeOdd = W.P.primaryOdd ∧
        S.distinguishedOpposite = !W.P.distinguishedOpposite := by
  classical
  let O := outerFrame F A u hbase
  let B := oppositeSelectedFrame F (by omega)
  let N₀ := nextFrame B A u hbase
  let N₁ := nextFrame F A u hbase
  let hN : 3 ≤ N₀.base.length := by simpa only [N₀, nextFrame] using hA
  let plift := pMarkedParentLift F A u hbase hA
  let prior := W.P.walk.map plift
  let oldK := W.P.K.image (Sym2.map plift)
  let oldH := W.P.H.image (Sym2.map plift)
  let d := W.P.distinguished.map plift
  let cross := W.P.crossing.map plift
  let jointrest := W.P.jointRest.map (mapPiece plift)
  let old₀ := W.P.primary.map plift
  let old₁ := W.P.opposite.map plift
  let primaryrest := W.P.primaryRest.map (mapPiece plift)
  let oppositerest := W.P.oppositeRest.map (mapPiece plift)
  obtain ⟨hprior, hp, ho, _, _⟩ :=
    native_actual_identity_two_order_state_transport _ _ plift (fun _ => rfl)
      F W.P.oppositeFrame W.P.primaryOdd W.P.oppositeOdd W.P.walk W.P.K W.P.H
      (⟨W.P.left, W.P.far, W.P.distinguished⟩ ::
        ⟨W.P.right, W.P.otherLeft, W.P.crossing⟩ :: W.P.jointRest)
      (⟨W.P.left, W.P.primaryFar, W.P.primary⟩ :: W.P.primaryRest)
      (⟨W.P.otherLeft, W.P.oppositeFar, W.P.opposite⟩ :: W.P.oppositeRest)
      W.P.partitions W.P.primaryBoundary W.P.oppositeBoundary
  have hfirst : s(plift W.P.right, plift W.P.left) ∈ oldK :=
    Finset.mem_image.mpr ⟨s(W.P.right, W.P.left), W.P.firstCut, rfl⟩
  have hℓ : (plift W.P.left).val = leftPort F 0 := W.P.leftCoordinate
  have hx : (plift W.P.otherLeft).val = leftPort B 0 := by
    change W.P.otherLeft.val = leftPort B 0
    simpa only [W.P.canonicalOpposite] using W.P.otherLeftCoordinate
  have hy₀ : (plift W.P.primaryFar).val = leftPort F (k - 1) := W.P.primaryFarCoordinate
  have hy₁ : (plift W.P.oppositeFar).val = leftPort B (k - 1) := by
    change W.P.oppositeFar.val = leftPort B (k - 1)
    simpa only [W.P.canonicalOpposite] using W.P.oppositeFarCoordinate
  have hb₀ : NativeBoundaryPairs F W.P.primaryOdd Subtype.val primaryrest := by
    intro p hmem
    exact hp p (List.mem_cons_of_mem _ hmem)
  have hb₁ : NativeBoundaryPairs B W.P.oppositeOdd Subtype.val oppositerest := by
    intro p hmem
    simpa only [W.P.canonicalOpposite] using ho p (List.mem_cons_of_mem _ hmem)
  obtain ⟨primary₀, primary₁, opposite₀, opposite₁, hs, hbprimary, hbopposite, hseam, _⟩ :=
    native_actual_simultaneous_boundary_state hm hk F B A u hbase hbase
      W.P.primaryOdd W.P.oppositeOdd Subtype.val Subtype.val_injective
      prior d cross jointrest old₀ primaryrest old₁ oppositerest oldK oldH
      hprior hfirst hℓ hx hy₀ hy₁ hb₀ hb₁ W.cycle W.hamiltonian
      J.new₀ J.new₁ J.new₂ J.K J.H J.disjoint J.partition
      J.zero₀ J.zero₁ J.erase₀ J.erase₁ J.left₀ J.right₀ J.left₁ J.right₁
  let jointTail : List (Piece (domainGraph (ParentDomain O))) :=
    ⟨J.r₁, plift W.P.left, J.new₂⟩ ::
      ⟨plift W.P.right, plift W.P.otherLeft, cross⟩ :: jointrest
  let primaryTail : List (Piece (domainGraph (ParentDomain O))) :=
    ⟨J.r₀, plift W.P.otherLeft, primary₁⟩ :: oppositerest
  let oppositeTail : List (Piece (domainGraph (ParentDomain O))) :=
    ⟨J.r₁, plift W.P.left, opposite₁⟩ :: primaryrest
  let joint := ⟨J.ℓ₀, plift W.P.far, J.new₀.reverse⟩ :: ⟨J.r₀, J.ℓ₁, J.new₁⟩ :: jointTail
  let primary := ⟨J.ℓ₀, plift W.P.oppositeFar, primary₀⟩ :: primaryTail
  let opposite := ⟨J.ℓ₁, plift W.P.primaryFar, opposite₀⟩ :: oppositeTail
  have hselected : F.selected.toFinset = B.selected.toFinset := by
    have h := W.P.sameSelected
    rw [W.P.canonicalOpposite] at h
    exact h.symm
  let middle := parentOrderDomainMap F B A u hbase hbase hselected rfl
  let lift := (parentNextMarkedMap B A u hbase hA).comp middle
  have hbij : Function.Bijective lift :=
    (parent_next_marked_map_bijective B A u hbase hA).comp
      (parent_order_domain_map_bijective F B A u hbase hbase hselected rfl)
  have hval : ∀ x, (lift x).val = x.val := fun _ => rfl
  have hBopp : oppositeSelectedFrame B (by omega) = F :=
    native_opposite_selected_involutive F (by omega)
  have hcan : oppositeSelectedFrame N₀ (by omega) = N₁ := by
    change oppositeSelectedFrame (nextFrame B A u hbase) (by omega) = _
    rw [native_opposite_next_frame B (by omega) A u hbase]
    simpa only [hBopp, N₁]
  obtain ⟨hstate, hprimary, hopposite, hKraw, hHraw⟩ :=
    native_actual_identity_two_order_state_transport _ _ lift hval N₀ N₁
      W.P.oppositeOdd W.P.primaryOdd W.cycle J.K J.H joint primary opposite
      hs hbprimary hbopposite
  have hshift₀ : leftPort F (k - 1) = leftPort N₁ k := by
    simpa only [show k - 1 + 1 = k by omega] using
      (native_marked_index_shift hm F A u hbase (k - 1)).2.symm
  have hshift₁ : leftPort B (k - 1) = leftPort N₀ k := by
    simpa only [show k - 1 + 1 = k by omega] using
      (native_marked_index_shift hm B A u hbase (k - 1)).2.symm
  have hfar : (lift (plift W.P.far)).val =
      leftPort (if !W.P.distinguishedOpposite then N₁ else N₀) k := by
    change W.P.far.val = _
    have h := W.P.farCoordinate
    rw [W.P.canonicalOpposite] at h
    cases hd : W.P.distinguishedOpposite
    · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      simpa only [hd, Bool.not_false, ↓reduceIte] using h.trans hshift₀
    · simp only [hd, ↓reduceIte] at h
      simpa only [hd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using h.trans hshift₁
  have hpair : s(protectedP N₀ (by omega), protectedQ N₀ (by omega)) =
      s(protectedP F (by omega), protectedQ F (by omega)) := by
    have hn := native_protected_labels_prepend B N₀ (by omega) u rfl
    rw [hn.1, hn.2]
    exact (by
      rw [(native_opposite_protected_labels F (by omega)).1,
        (native_opposite_protected_labels F (by omega)).2, Sym2.eq_swap])
  have hselNext : N₀.selected.toFinset = insert u F.selected.toFinset := by
    simp only [N₀, nextFrame, List.toFinset_cons]
    rw [← hselected]
  obtain ⟨hAkeep, hBkeep, hCkeep⟩ := state_parent_retention hm F (by omega) A u hbase hA W
  let w := W.cycle.map lift
  have hA' : ∀ (x y : {z : Configuration m // SpecialDomain N₀ hN z}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠
        s(protectedP N₀ (by omega), protectedQ N₀ (by omega)) → s(x, y) ∈ w.edges := by
    intro x y hy hp
    obtain ⟨x', rfl⟩ := hbij.surjective x
    obtain ⟨y', rfl⟩ := hbij.surjective y
    rw [hval, hval] at hy hp
    rw [hpair] at hp
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), hAkeep x' y' hy hp, rfl⟩
  have hB' : ∀ (x y : {z : Configuration m // SpecialDomain N₀ hN z}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ N₀.selected.toFinset → s(x, y) ∈ w.edges := by
    intro x y hy ht
    obtain ⟨x', rfl⟩ := hbij.surjective x
    obtain ⟨y', rfl⟩ := hbij.surjective y
    rw [hval, hval] at hy
    rw [hval, hselNext] at ht
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), hBkeep x' y' hy ht, rfl⟩
  have rawmap : Sym2.map Subtype.val ∘ Sym2.map lift =
      (Sym2.map Subtype.val : Sym2 _ → Sym2 (Configuration m)) := by
    funext e
    rw [Function.comp_apply, Sym2.map_map]
    rfl
  have hC' : ∀ x : Configuration m, s(x, x * c m) ∈ w.edges.map (Sym2.map Subtype.val) →
      x (Fin.last m) ∈ N₀.selected.toFinset := by
    intro x hx
    change s(x, x * c m) ∈ (W.cycle.map lift).edges.map (Sym2.map Subtype.val) at hx
    rw [SimpleGraph.Walk.edges_map, List.map_map, rawmap] at hx
    rw [hselNext]
    exact hCkeep x hx
  let S : StateFor N₀ (by omega) hN := {
    oppositeFrame := N₁
    canonicalOpposite := hcan.symm
    sameSelected := by
      simp only [N₀, N₁, nextFrame, List.toFinset_cons]
      rw [hselected]
    sameBase := rfl
    sameTerminal := rfl
    sameProtectedPair := by
      rw [← hcan, (native_opposite_protected_labels N₀ (by omega)).1,
        (native_opposite_protected_labels N₀ (by omega)).2, Sym2.eq_swap]
    primaryOdd := W.P.oppositeOdd
    oppositeOdd := W.P.primaryOdd
    distinguishedOpposite := !W.P.distinguishedOpposite
    base := lift W.base
    walk := w
    hamiltonian := SimpleGraph.Walk.IsHamiltonianCycle.map hbij W.hamiltonian
    K := J.K.image (Sym2.map lift)
    H := J.H.image (Sym2.map lift)
    primaryCuts := hKraw.trans J.primaryCuts
    oppositeCuts := hHraw.trans J.oppositeCuts
    left := lift J.ℓ₀
    right := lift J.r₀
    otherLeft := lift J.ℓ₁
    far := lift (plift W.P.far)
    primaryFar := lift (plift W.P.oppositeFar)
    oppositeFar := lift (plift W.P.primaryFar)
    leftCoordinate := J.left₀
    rightCoordinate := J.right₀
    otherLeftCoordinate := J.left₁
    farCoordinate := by simpa only [Nat.add_sub_cancel] using hfar
    primaryFarCoordinate := by
      simpa only [hval, Nat.add_sub_cancel] using hy₁.trans hshift₁
    oppositeFarCoordinate := by
      simpa only [hval, Nat.add_sub_cancel] using hy₀.trans hshift₀
    distinguished := J.new₀.reverse.map lift
    crossing := J.new₁.map lift
    jointRest := jointTail.map (mapPiece lift)
    primary := primary₀.map lift
    primaryRest := primaryTail.map (mapPiece lift)
    opposite := opposite₀.map lift
    oppositeRest := oppositeTail.map (mapPiece lift)
    partitions := by simpa only [joint, primary, opposite, List.map_cons, mapPiece] using hstate
    primaryBoundary := by simpa only [primary, List.map_cons, mapPiece] using hprimary
    oppositeBoundary := by simpa only [opposite, List.map_cons, mapPiece] using hopposite
    firstCut := Finset.mem_image.mpr ⟨s(J.r₀, J.ℓ₀), hseam, rfl⟩
    keepsProtectedA := hA'
    keepsRemainingB := hB'
    selectedC := hC' }
  exact ⟨S, rfl, rfl, rfl⟩

#print axioms strong_state_from_same_parent

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStrongStateStep
