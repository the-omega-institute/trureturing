/- Candidate for the general k step. Not yet kernel checked.
   The state walk remains the supplier throughout each construction. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedFrameDomains
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeMarkedStepCoordinates
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSimultaneousBoundaryState
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open private pChildIndex outer_base_bound old_base_bound from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
open private anchor_coordinates bc_terminal from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open private special_child_path from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveCycleStep
open private parentPiece from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeOuterChildAssembly
open private frame_terminal_fresh from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansionDomains

private theorem primary_actual_partition {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (S : StateFor F hk hB) :
    ActualCyclePartition S.walk (specialCuts hm F hB)
      (⟨S.left, S.primaryFar, S.primary⟩ :: S.primaryRest) := by
  classical
  have hraw : (specialCuts hm F hB).image (Sym2.map Subtype.val) = markedCuts F := by
    simp only [specialCuts, Finset.image_image, markedCuts]
    congr 1
    funext i
    rfl
  have hcuts : S.K = specialCuts hm F hB :=
    Finset.image_injective (Sym2.map.injective Subtype.val_injective)
      (S.primaryCuts.trans hraw.symm)
  rw [← hcuts]
  exact S.partitions.primary_partition

private theorem even_special_from_state {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 2)) (hB : 3 ≤ F.base.length)
    (S : StateFor F (by omega) hB) (hodd : S.primaryOdd = false) :
    ∃ ordered : Fin (2 * s + 3) → Piece (domainGraph (SpecialDomain F hB)),
      ∃ q : (domainGraph (SpecialDomain F hB)).Walk
        (specialVertex hm F hB (0, 0))
        (specialVertex hm F hB (Fin.last (2 * s + 2), 1)),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start = specialVertex hm F hB
          (evenPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (ordered i).finish = specialVertex hm F hB
          (evenPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0)
        (List.ofFn fun i : Fin (2 * s + 2) => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ S.walk.edgeSet ∧ e ∉ specialCuts hm F hB := by
  have hp := primary_actual_partition hm F (by omega) hB S
  exact native_special_child_even_path hm s F hB S.walk S.hamiltonian
    (⟨S.left, S.primaryFar, S.primary⟩ :: S.primaryRest)
    hp.support hp.edges hp.cut_mem (by
      simpa only [NativeBoundaryPairs, hodd, Bool.false_eq_true, ↓reduceIte] using
        S.primaryBoundary)

private theorem odd_special_from_state {m : ℕ} (hm : 3 ≤ m) (s : ℕ)
    (F : SupplyFrame m (2 * s + 3)) (hB : 3 ≤ F.base.length)
    (S : StateFor F (by omega) hB) (hodd : S.primaryOdd = true) :
    ∃ ordered : Fin (2 * s + 4) → Piece (domainGraph (SpecialDomain F hB)),
      ∃ q : (domainGraph (SpecialDomain F hB)).Walk
        (specialVertex hm F hB (0, 0))
        (specialVertex hm F hB (Fin.last (2 * s + 3), 1)),
      q.IsHamiltonian ∧
      (∀ i, (ordered i).start = specialVertex hm F hB
          (oddPortRoute s ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
        (ordered i).finish = specialVertex hm F hB
          (oddPortRoute s ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)) ∧
      q.support = (List.ofFn ordered).flatMap (fun z => z.walk.support) ∧
      q.edges = chainEdges (ordered 0)
        (List.ofFn fun i : Fin (2 * s + 3) => ordered i.succ) ∧
      ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
        e ∈ S.walk.edgeSet ∧ e ∉ specialCuts hm F hB := by
  have hp := primary_actual_partition hm F (by omega) hB S
  exact native_special_child_odd_path hm s F hB S.walk S.hamiltonian
    (⟨S.left, S.primaryFar, S.primary⟩ :: S.primaryRest)
    hp.support hp.edges hp.cut_mem (by
      simpa only [NativeBoundaryPairs, hodd, ↓reduceIte] using S.primaryBoundary)

/-- The final ordinary child uses exactly the old state walk. Its
    supplier edge is earned from the remaining-b invariant. -/
private theorem old_p_specified_from_state {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (S : StateFor F hk (old_base_bound F A u hbase hA)) :
    ∃ C : SpecifiedOrdinaryCycle hm (outerFrame F A u hbase)
        (outer_base_bound F A u hbase hA) (pChildIndex F A u hbase)
        (by change 0 < A.length; omega),
      ∃ hb : C.base = pMarkedChildMap F A u hbase hA S.base,
        C.walk.copy hb hb = S.walk.map (pMarkedChildMap F A u hbase hA) := by
  classical
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let j := pChildIndex F A u hbase
  have hj : 0 < j.val := by change 0 < A.length; omega
  let lift := pMarkedChildMap F A u hbase hA
  let r := ordinaryRight hm O hBO j hj
  let l := ordinaryLeft hm O hBO j hj
  let r' : {v : Configuration m // SpecialDomain F (old_base_bound F A u hbase hA) v} :=
    ⟨r.val, (native_p_marked_domain_eq_child F A u hbase hA r.val).mpr r.property⟩
  let l' : {v : Configuration m // SpecialDomain F (old_base_bound F A u hbase hA) v} :=
    ⟨l.val, (native_p_marked_domain_eq_child F A u hbase hA l.val).mpr l.property⟩
  have hterminal : r'.val (Fin.last m) ∉ F.selected.toFinset := by
    rw [show r'.val = rightPort O (k + j.val) by rfl]
    rw [rightPort, bc_terminal (by omega : 2 ≤ m), (anchor_coordinates O).2]
    change O.terminal ∉ O.selected.toFinset
    simp only [List.mem_toFinset]
    exact fun h => frame_terminal_fresh O (List.mem_append.mpr (Or.inl h))
  have hcut : s(r, l) ∈ (S.walk.map lift).edgeSet := by
    change s(r, l) ∈ (S.walk.map lift).edges
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(r', l'), S.keepsRemainingB r' l' rfl hterminal, rfl⟩
  exact ⟨⟨lift S.base, S.walk.map lift,
    SimpleGraph.Walk.IsHamiltonianCycle.map
      (p_marked_child_map_bijective F A u hbase hA) S.hamiltonian, hcut⟩,
    rfl, rfl⟩


/-- All route data is attached to this particular state walk. -/
private structure SpecialPathFromState {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (S : StateFor F hk hB) where
  route : Fin (2 * (k + 1)) → Port k
  ordered : Fin (k + 1) → Piece (domainGraph (SpecialDomain F hB))
  path : (domainGraph (SpecialDomain F hB)).Walk
    (specialVertex hm F hB (0, 0)) (specialVertex hm F hB (Fin.last k, 1))
  hamiltonian : path.IsHamiltonian
  orderedPorts : ∀ i,
    (ordered i).start = specialVertex hm F hB
      (route ⟨2 * i.val, by have hi := i.isLt; omega⟩) ∧
    (ordered i).finish = specialVertex hm F hB
      (route ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)
  support : path.support = (List.ofFn ordered).flatMap fun z => z.walk.support
  edges : path.edges = chainEdges (ordered 0) (List.ofFn fun i : Fin k => ordered i.succ)
  uncutInventory : ∀ e, e ∈ ((List.ofFn ordered).flatMap fun z => z.walk.edges) ↔
    e ∈ S.walk.edgeSet ∧ e ∉ specialCuts hm F hB

private theorem special_path_from_state {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (S : StateFor F hk hB) (hodd : S.primaryOdd = decide (k % 2 = 1)) :
    Nonempty (SpecialPathFromState hm F hk hB S) := by
  by_cases he : k % 2 = 0
  · obtain ⟨s, rfl⟩ : ∃ s, k = 2 * s + 2 := ⟨(k - 2) / 2, by omega⟩
    obtain ⟨ordered, q, hq, hp, hs, hedges, hinv⟩ :=
      even_special_from_state hm s F hB S (by
        simpa only [he, Nat.zero_ne_one, decide_false] using hodd)
    exact ⟨⟨evenPortRoute s, ordered, q, hq, hp, hs, hedges, hinv⟩⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = 2 * s + 3 := ⟨(k - 3) / 2, by omega⟩
    have hrem : (2 * s + 3) % 2 = 1 := by omega
    obtain ⟨ordered, q, hq, hp, hs, hedges, hinv⟩ :=
      odd_special_from_state hm s F hB S (by
        simpa only [hrem, decide_true] using hodd)
    exact ⟨⟨oddPortRoute s, ordered, q, hq, hp, hs, hedges, hinv⟩⟩

private structure OrdinaryFromState {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    (S : StateFor (nativeChildFrame F j) hk
      (by simpa only [nativeChildFrame, List.length_rotate] using hB)) where
  cycle : SpecifiedOrdinaryCycle hm F hB j hj
  mappedBase : cycle.base = childMarkedDomainMap F hB j S.base
  mappedWalk : cycle.walk.copy mappedBase mappedBase =
    S.walk.map (childMarkedDomainMap F hB j)

private theorem ordinary_from_state {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (j : Fin F.base.length) (hj : 0 < j.val)
    (S : StateFor (nativeChildFrame F j) hk
      (by simpa only [nativeChildFrame, List.length_rotate] using hB)) :
    Nonempty (OrdinaryFromState hm F hk hB j hj S) := by
  obtain ⟨C, hb, hw, _, _, _⟩ :=
    native_child_frame_specified_ordinary hm F hB j hj S.walk
      S.hamiltonian S.keepsRemainingB
  exact ⟨⟨C, hb, hw⟩⟩

/-- Same-witness parent data for the arbitrary-k driver. Unlike an
existence of an unrelated parent, every old state and its actual mapped
cycle can be used by the later joint and two-order boundary update. -/
private structure OuterStateParentFor {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) where
  P : StateFor F hk (old_base_bound F A u hbase hA)
  Q : StateFor (outerFrame F A u hbase) hk (outer_base_bound F A u hbase hA)
  pFlags : P.primaryOdd = decide (k % 2 = 1) ∧
    P.oppositeOdd = !decide (k % 2 = 1) ∧ P.distinguishedOpposite = decide (k % 2 = 0)
  qFlags : Q.primaryOdd = decide (k % 2 = 1) ∧
    Q.oppositeOdd = !decide (k % 2 = 1) ∧ Q.distinguishedOpposite = decide (k % 2 = 0)
  special : SpecialPathFromState hm (outerFrame F A u hbase) hk
    (outer_base_bound F A u hbase hA) Q
  oldP : SpecifiedOrdinaryCycle hm (outerFrame F A u hbase)
    (outer_base_bound F A u hbase hA) (pChildIndex F A u hbase)
    (by change 0 < A.length; omega)
  oldPBase : oldP.base = pMarkedChildMap F A u hbase hA P.base
  oldPWalk : oldP.walk.copy oldPBase oldPBase = P.walk.map (pMarkedChildMap F A u hbase hA)
  otherStates : ∀ (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val),
    StateFor (nativeChildFrame (outerFrame F A u hbase) j) hk
      (by simpa only [nativeChildFrame, List.length_rotate] using
        outer_base_bound F A u hbase hA)
  otherCycles : ∀ j hj, OrdinaryFromState hm (outerFrame F A u hbase) hk
    (outer_base_bound F A u hbase hA) j hj (otherStates j hj)
  children : ∀ (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val),
    SpecifiedOrdinaryCycle hm (outerFrame F A u hbase)
      (outer_base_bound F A u hbase hA) j hj
  oldPAttached : children (pChildIndex F A u hbase) (by change 0 < A.length; omega) = oldP
  otherAttached : ∀ j hj, j ≠ pChildIndex F A u hbase →
    children j hj = (otherCycles j hj).cycle
  paths : ∀ j : Fin (outerFrame F A u hbase).base.length,
    ActualChildPath (outerFrame F A u hbase) j
  specialPath : (paths ⟨0, by
      simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩).piece =
    (special_child_path hm (outerFrame F A u hbase)
      (outer_base_bound F A u hbase hA) special.path special.hamiltonian).piece
  ordinaryInventory : ∀ j hj, ∀ e,
    e ∈ (paths j).piece.walk.edges ↔ e ∈ (children j hj).walk.edges ∧
      e ≠ s(ordinaryRight hm (outerFrame F A u hbase)
        (outer_base_bound F A u hbase hA) j hj,
        ordinaryLeft hm (outerFrame F A u hbase) (outer_base_bound F A u hbase hA) j hj)
  pieces : Fin (outerFrame F A u hbase).base.length →
    Piece (domainGraph (ParentDomain (outerFrame F A u hbase)))
  base : {x : Configuration m // ParentDomain (outerFrame F A u hbase) x}
  cycle : (domainGraph (ParentDomain (outerFrame F A u hbase))).Walk base base
  childPieces : ∀ j, pieces j = parentPiece (outerFrame F A u hbase) j (paths j)
  baseCoordinate : base.val = rightPort (outerFrame F A u hbase) 0
  hamiltonian : cycle.IsHamiltonianCycle
  support : cycle.support.tail = ((List.ofFn pieces).flatMap fun z => z.walk.support).reverse
  edges : cycle.edges = s(base, (pieces (pChildIndex F A u hbase)).finish) ::
    (chainEdges (pieces ⟨0, by
      simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩)
      (List.ofFn fun i : Fin ((outerFrame F A u hbase).base.length - 1) =>
        pieces ⟨i.val + 1, by
          have hi := i.isLt
          simp only [outerFrame, List.length_append, List.length_singleton] at hi ⊢
          omega⟩)).reverse


private theorem parent_from_state_suppliers {m k : ℕ} (hm : 3 ≤ m)
    (hk : 2 ≤ k)
    (prior : ∀ (G : SupplyFrame m k) (hB : 3 ≤ G.base.length),
      ∃ S : StateFor G hk hB, S.primaryOdd = decide (k % 2 = 1) ∧
        S.oppositeOdd = !decide (k % 2 = 1) ∧ S.distinguishedOpposite = decide (k % 2 = 0))
    (F : SupplyFrame m k) (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length) :
    Nonempty (OuterStateParentFor hm F hk A u hbase hA) := by
  classical
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  let jP := pChildIndex F A u hbase
  have hjP : 0 < jP.val := by change 0 < A.length; omega
  obtain ⟨P, hP⟩ := prior F (old_base_bound F A u hbase hA)
  obtain ⟨Q, hQ⟩ := prior O hBO
  let special := Classical.choice (special_path_from_state hm O hk hBO Q hQ.1)
  obtain ⟨oldP, hPbase, hPwalk⟩ := old_p_specified_from_state hm F hk A u hbase hA P
  let states (j : Fin O.base.length) (hj : 0 < j.val) :=
    Classical.choose (prior (nativeChildFrame O j)
      (by simpa only [nativeChildFrame, List.length_rotate] using hBO))
  let ordinary (j : Fin O.base.length) (hj : 0 < j.val) :=
    Classical.choice (ordinary_from_state hm O hk hBO j hj (states j hj))
  let children (j : Fin O.base.length) (hj : 0 < j.val) :
      SpecifiedOrdinaryCycle hm O hBO j hj :=
    if he : j = jP then he.symm ▸ oldP else (ordinary j hj).cycle
  have hp : children jP hjP = oldP := by simp only [children, dif_pos rfl]
  have ho : ∀ j hj, j ≠ jP → children j hj = (ordinary j hj).cycle := by
    intro j hj hne
    simp only [children, dif_neg hne]
  obtain ⟨paths, hspecial, hordinary, pieces, base, c, hpieces, hbase', hc, hs, he⟩ :=
    recursive_cycle_from_specified_children_with_inventory hm
      O hBO special.path special.hamiltonian children
  have hlast : (⟨O.base.length - 1, by
      simp only [O, outerFrame, List.length_append, List.length_singleton]
      omega⟩ : Fin O.base.length) = jP := by
    apply Fin.ext
    simp only [O, outerFrame, List.length_append, List.length_singleton, jP, pChildIndex]
    omega
  rw [hlast] at he
  exact ⟨⟨P, Q, hP, hQ, special, oldP, hPbase, hPwalk, states, ordinary,
    children, hp, ho, paths, hspecial, hordinary,
    pieces, base, c, hpieces, hbase', hc, hs, he⟩⟩

#print axioms parent_from_state_suppliers

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
