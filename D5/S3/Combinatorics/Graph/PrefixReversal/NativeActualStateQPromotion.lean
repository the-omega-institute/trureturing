/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateQPromotion
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateQPromotion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Slice the special path already used by the actual parent. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStatePromotion
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBoundarySlicing

set_option autoImplicit false
-- The saved child-domain identities unfold across the dependent frame maps.
set_option backward.isDefEq.respectTransparency.types false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateQPromotion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeOppositeSelectedOrders
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualQBoundarySlicing
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
open private outer_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses

private theorem same_state_q_three_fragments {m k : ℕ} (hm : 3 ≤ m) (hk : 3 ≤ k)
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F (by omega) A u hbase hA) :
    let O := outerFrame F A u hbase
    let hBO := outer_base_bound F A u hbase hA
    let B := oppositeSelectedFrame F (by omega)
    let N₀ := nextFrame B A u hbase
    let N₁ := nextFrame F A u hbase
    ∃ r₀ ℓ₀ r₁ ℓ₁ : {x : Configuration m // SpecialDomain O hBO x},
      r₀.val = rightPort N₀ 0 ∧ ℓ₀.val = leftPort N₀ 0 ∧
      r₁.val = rightPort N₁ 0 ∧ ℓ₁.val = leftPort N₁ 0 ∧
      ∃ q₀ : (domainGraph (SpecialDomain O hBO)).Walk
          (specialVertex hm O hBO (0, 0)) ℓ₀,
        ∃ q₁ : (domainGraph (SpecialDomain O hBO)).Walk r₀ ℓ₁,
        ∃ q₂ : (domainGraph (SpecialDomain O hBO)).Walk r₁
          (specialVertex hm O hBO (Fin.last k, 1)),
          q₀.IsPath ∧ q₁.IsPath ∧ q₂.IsPath ∧
          q₀.support ++ q₁.support ++ q₂.support = W.special.path.support ∧
          q₀.edges ++ [s(ℓ₀, r₀)] ++ q₁.edges ++ [s(ℓ₁, r₁)] ++ q₂.edges =
            W.special.path.edges ∧
          q₀.edges ++ q₁.edges ++ q₂.edges = W.special.path.edges.filter
            (fun e => decide (e ≠ s(ℓ₀, r₀) ∧ e ≠ s(ℓ₁, r₁))) := by
  classical
  dsimp only
  let O := outerFrame F A u hbase
  let B := oppositeSelectedFrame F (by omega)
  let OB := outerFrame B A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let hBB := outer_base_bound B A u hbase hA
  have hQopp : W.Q.oppositeFrame = OB := by
    rw [W.Q.canonicalOpposite, native_opposite_outer_frame F (by omega) A u hbase]
  have hselected : F.selected.toFinset = B.selected.toFinset := by
    have h := W.P.sameSelected
    rw [W.P.canonicalOpposite] at h
    exact h.symm
  have hN₁ := native_new_marked_cut_domains hm F A u hbase hA 0
  have hN₀ := native_new_marked_cut_domains hm B A u hbase hA 0
  have horders (x) : SpecialDomain OB hBB x ↔ SpecialDomain O hBO x :=
    native_marked_orders_same_domain OB O hBB hBO hselected.symm rfl rfl x
  let r₀ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨rightPort (nextFrame B A u hbase) 0, (horders _).mp hN₀.1⟩
  let ℓ₀ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨leftPort (nextFrame B A u hbase) 0, (horders _).mp hN₀.2⟩
  let r₁ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨rightPort (nextFrame F A u hbase) 0, hN₁.1⟩
  let ℓ₁ : {x : Configuration m // SpecialDomain O hBO x} :=
    ⟨leftPort (nextFrame F A u hbase) 0, hN₁.2⟩
  let joint := ⟨W.Q.left, W.Q.far, W.Q.distinguished⟩ ::
    ⟨W.Q.right, W.Q.otherLeft, W.Q.crossing⟩ :: W.Q.jointRest
  let jp : Piece (domainGraph (SpecialDomain O hBO)) :=
    ⟨W.Q.right, W.Q.otherLeft, W.Q.crossing⟩
  have hjp : jp ∈ joint := by simp only [joint, jp, List.mem_cons, true_or, or_true]
  have hjs : jp.start.val = rightPort O 0 := W.Q.rightCoordinate
  have hjf : jp.finish.val = leftPort OB 0 := by
    rw [W.Q.otherLeftCoordinate, hQopp]
  have hK : W.Q.K.image (Sym2.map Subtype.val) = markedCuts O := W.Q.primaryCuts
  have hH : W.Q.H.image (Sym2.map Subtype.val) = markedCuts OB := by
    rw [W.Q.oppositeCuts, hQopp]
  have hKS : W.Q.K = specialCuts hm O hBO := by
    apply Finset.image_injective (Sym2.map.injective Subtype.val_injective)
    rw [hK]
    simp only [specialCuts, Finset.image_image, markedCuts]
    congr 1
  have hji (e) : e ∈ joint.flatMap (fun z => z.walk.edges) ↔
      e ∈ W.Q.walk.edges ∧ e ∉ W.Q.K ∪ W.Q.H := by
    rw [W.Q.partitions.joint_partition.edges.mem_iff]
    simp only [List.mem_filter, decide_eq_true_eq]
  have hbi (e) : e ∈ (List.ofFn W.special.ordered).flatMap (fun z => z.walk.edges) ↔
      e ∈ W.Q.walk.edges ∧ e ∉ W.Q.K := by
    rw [hKS]
    exact W.special.uncutInventory e
  have hprotect := native_protected_labels O (by omega : 2 ≤ k)
  rcases W.special.routeSelection with ⟨s, hshape, hroute⟩ | ⟨s, hshape, hroute⟩
  · subst k
    have hr : W.special.route = evenPortRoute s := eq_of_heq hroute
    have hend : ∀ i,
        (W.special.ordered i).start = specialVertex hm O hBO
          (evenPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (W.special.ordered i).finish = specialVertex hm O hBO
          (evenPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) := by
      intro i
      simpa only [hr] using W.special.orderedPorts i
    obtain ⟨q₀, q₁, q₂, hp₀, hp₁, hp₂, hs, he, hf⟩ :=
      native_actual_q_even_three_fragments hm s F B A u hbase hbase hA hselected
        (protectedP O (by omega)) (protectedQ O (by omega))
        (List.mem_toFinset.mpr hprotect.2.1) (List.mem_toFinset.mpr hprotect.2.2.1)
        W.Q.walk W.Q.hamiltonian W.Q.keepsProtectedA W.Q.keepsRemainingB
        joint W.Q.partitions.joint_partition.support jp hjp hjs hjf
        W.special.ordered hend W.special.path W.special.hamiltonian W.special.support
        W.Q.K W.Q.H hK hH hji hbi
        (r₀ := r₀) (ℓ₀ := ℓ₀) (r₁ := r₁) (ℓ₁ := ℓ₁) rfl rfl rfl rfl
    exact ⟨r₀, ℓ₀, r₁, ℓ₁, rfl, rfl, rfl, rfl,
      q₀, q₁, q₂, hp₀, hp₁, hp₂, hs, he, hf⟩
  · subst k
    have hr : W.special.route = oddPortRoute s := eq_of_heq hroute
    have hend : ∀ i,
        (W.special.ordered i).start = specialVertex hm O hBO
          (oddPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (W.special.ordered i).finish = specialVertex hm O hBO
          (oddPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩) := by
      intro i
      simpa only [hr] using W.special.orderedPorts i
    obtain ⟨q₀, q₁, q₂, hp₀, hp₁, hp₂, hs, he, hf⟩ :=
      native_actual_q_odd_three_fragments hm s F B A u hbase hbase hA hselected
        (protectedP O (by omega)) (protectedQ O (by omega))
        (List.mem_toFinset.mpr hprotect.2.1) (List.mem_toFinset.mpr hprotect.2.2.1)
        W.Q.walk W.Q.hamiltonian W.Q.keepsProtectedA W.Q.keepsRemainingB
        joint W.Q.partitions.joint_partition.support jp hjp hjs hjf
        W.special.ordered hend W.special.path W.special.hamiltonian W.special.support
        W.Q.K W.Q.H hK hH hji hbi
        (r₀ := r₀) (ℓ₀ := ℓ₀) (r₁ := r₁) (ℓ₁ := ℓ₁) rfl rfl rfl rfl
    exact ⟨r₀, ℓ₀, r₁, ℓ₁, rfl, rfl, rfl, rfl,
      q₀, q₁, q₂, hp₀, hp₁, hp₂, hs, he, hf⟩

#print axioms same_state_q_three_fragments

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateQPromotion
