/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateSuppliers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserve the chosen old states and parent opening inventories. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualInductionState
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2ParentWitnesses
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSelectedCInvariant

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
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeProtectedLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.RecursivePortBoundary
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.ActualSimultaneousBoundaryAdvance
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJointMarkedCutShift
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
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
structure SpecialPathFromState {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k) (hB : 3 ≤ F.base.length)
    (S : StateFor F hk hB) where
  route : Fin (2 * (k + 1)) → Port k
  routeSelection : (∃ s, k = 2 * s + 2 ∧ HEq route (evenPortRoute s)) ∨
    (∃ s, k = 2 * s + 3 ∧ HEq route (oddPortRoute s))
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
    exact ⟨⟨evenPortRoute s, Or.inl ⟨s, rfl, HEq.rfl⟩, ordered, q, hq, hp, hs, hedges, hinv⟩⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = 2 * s + 3 := ⟨(k - 3) / 2, by omega⟩
    have hrem : (2 * s + 3) % 2 = 1 := by omega
    obtain ⟨ordered, q, hq, hp, hs, hedges, hinv⟩ :=
      odd_special_from_state hm s F hB S (by
        simpa only [hrem, decide_true] using hodd)
    exact ⟨⟨oddPortRoute s, Or.inr ⟨s, rfl, HEq.rfl⟩, ordered, q, hq, hp, hs, hedges, hinv⟩⟩

structure OrdinaryFromState {m k : ℕ} (hm : 3 ≤ m)
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
structure OuterStateParentFor {m k : ℕ} (hm : 3 ≤ m)
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


private structure Invariants {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (D : Configuration m → Prop) {base : {x // D x}}
    (w : (domainGraph D).Walk base base) : Prop where
  keepA : ∀ (x y : {z // D z}), y.val = x.val * a m →
    s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(protectedP F hk, protectedQ F hk) →
    s(x, y) ∈ w.edges
  keepB : ∀ (x y : {z // D z}), y.val = x.val * b m →
    x.val (Fin.last m) ∉ F.selected.toFinset → s(x, y) ∈ w.edges
  cLabels : ∀ e ∈ w.edges, ∀ x : Configuration m,
    Sym2.map Subtype.val e = s(x, x * c m) → x (Fin.last m) ∈ F.selected.toFinset

private theorem state_invariants {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (hB : 3 ≤ F.base.length) (S : StateFor F hk hB) :
    Invariants F hk (SpecialDomain F hB) S.walk := by
  refine ⟨S.keepsProtectedA, S.keepsRemainingB, ?_⟩
  intro e he x hx
  exact S.selectedC x (List.mem_map.mpr ⟨e, he, hx⟩)

private theorem invariants_map {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    {D E : Configuration m → Prop} {a : {x // D x}}
    (w : (domainGraph D).Walk a a) (h : Invariants F hk D w)
    (f : domainGraph D →g domainGraph E) (hf : Function.Bijective f)
    (hval : ∀ x, (f x).val = x.val) : Invariants F hk E (w.map f) := by
  constructor
  · intro x y hy hp
    obtain ⟨x', rfl⟩ := hf.surjective x
    obtain ⟨y', rfl⟩ := hf.surjective y
    rw [hval, hval] at hy hp
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), h.keepA x' y' hy hp, rfl⟩
  · intro x y hy ht
    obtain ⟨x', rfl⟩ := hf.surjective x
    obtain ⟨y', rfl⟩ := hf.surjective y
    rw [hval, hval] at hy
    rw [hval] at ht
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(x', y'), h.keepB x' y' hy ht, rfl⟩
  · intro e he x hx
    rw [SimpleGraph.Walk.edges_map] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    have hraw : Sym2.map Subtype.val (Sym2.map f e') = Sym2.map Subtype.val e' := by
      rw [Sym2.map_map]
      congr 1
      funext z
      exact hval z
    exact h.cLabels e' he' x (hraw.symm.trans hx)

private theorem invariants_of_edges {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (D : Configuration m → Prop) {a b : {x // D x}}
    (w : (domainGraph D).Walk a a) (v : (domainGraph D).Walk b b)
    (h : Invariants F hk D w) (he : v.edges = w.edges) : Invariants F hk D v := by
  constructor
  · intro x y hy hp; rw [he]; exact h.keepA x y hy hp
  · intro x y hy ht; rw [he]; exact h.keepB x y hy ht
  · intro e hm x hx; rw [he] at hm; exact h.cLabels e hm x hx

private theorem invariants_same_selected {m k : ℕ} (F G : SupplyFrame m k) (hk : 2 ≤ k)
    (hs : G.selected = F.selected) (D : Configuration m → Prop)
    {base : {x // D x}} (w : (domainGraph D).Walk base base)
    (h : Invariants F hk D w) : Invariants G hk D w := by
  constructor
  · intro x y hy hp
    apply h.keepA x y hy
    simpa only [protectedP, protectedQ, hs] using hp
  · intro x y hy ht
    exact h.keepB x y hy (by simpa only [hs] using ht)
  · intro e he x hx
    simpa only [hs] using h.cLabels e he x hx

private theorem outer_child_invariants {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA)
    (j : Fin (outerFrame F A u hbase).base.length) (hj : 0 < j.val) :
    Invariants (outerFrame F A u hbase) hk
      (ChildDomain (childGap (outerFrame F A u hbase) j)) (W.children j hj).walk := by
  by_cases he : j = pChildIndex F A u hbase
  · subst j
    rw [W.oldPAttached]
    have h := invariants_map F hk W.P.walk
      (state_invariants F hk _ W.P) (pMarkedChildMap F A u hbase hA)
      (p_marked_child_map_bijective F A u hbase hA) (fun _ => rfl)
    have hedges := congrArg (fun w => w.edges) W.oldPWalk
    simp only [SimpleGraph.Walk.edges_copy] at hedges
    exact invariants_same_selected F (outerFrame F A u hbase) hk rfl _ _
      (invariants_of_edges F hk _ _ _ h hedges)
  · rw [W.otherAttached j hj he]
    let O := outerFrame F A u hbase
    let G := nativeChildFrame O j
    have h := invariants_map G hk (W.otherStates j hj).walk
      (state_invariants G hk _ (W.otherStates j hj))
      (childMarkedDomainMap O (outer_base_bound F A u hbase hA) j)
      (child_marked_domain_map_bijective O (outer_base_bound F A u hbase hA) j) (fun _ => rfl)
    have hedges := congrArg (fun w => w.edges) (W.otherCycles j hj).mappedWalk
    simp only [SimpleGraph.Walk.edges_copy] at hedges
    exact invariants_same_selected G O hk rfl _ _
      (invariants_of_edges G hk _ _ _ h hedges)

private structure OpenInvariants {m k : ℕ} (F : SupplyFrame m k) (hk : 2 ≤ k)
    (D : Configuration m → Prop) {base finish : {x // D x}}
    (w : (domainGraph D).Walk base finish) : Prop where
  keepA : ∀ (x y : {z // D z}), y.val = x.val * a m →
    s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(protectedP F hk, protectedQ F hk) →
    s(x, y) ∈ w.edges
  keepB : ∀ (x y : {z // D z}), y.val = x.val * b m →
    x.val (Fin.last m) ∉ F.selected.toFinset → x.val (Fin.last m) ≠ F.terminal →
    s(x, y) ∈ w.edges
  cLabels : ∀ e ∈ w.edges, ∀ x : Configuration m,
    Sym2.map Subtype.val e = s(x, x * c m) →
      x (Fin.last m) ∈ insert F.terminal F.selected.toFinset

private theorem outer_opened_invariants {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA)
    (j : Fin (outerFrame F A u hbase).base.length) :
    OpenInvariants (outerFrame F A u hbase) hk
      (ChildDomain (childGap (outerFrame F A u hbase) j)) (W.paths j).piece.walk := by
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  by_cases hj : 0 < j.val
  · have h := outer_child_invariants hm F hk A u hbase hA W j hj
    constructor
    · intro x y hy hp
      exact native_other_path_keeps_a hm O hBO j hj (W.children j hj).walk
        (W.paths j) (W.ordinaryInventory j hj) x y hy (h.keepA x y hy hp)
    · intro x y hy ht hn
      exact native_other_path_keeps_remaining_b hm O hBO j hj (W.children j hj).walk
        (W.paths j) (W.ordinaryInventory j hj) x y hy hn (h.keepB x y hy ht)
    · intro e he x hx
      exact Finset.mem_insert_of_mem
        (h.cLabels e ((W.ordinaryInventory j hj e).mp he).1 x hx)
  · have hj0 : j = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 3) hBO⟩ := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    subst j
    rw [W.specialPath]
    change OpenInvariants O hk (SpecialDomain O hBO) W.special.path
    have h := state_invariants O hk hBO W.Q
    let p := W.special.ordered 0
    let ps := List.ofFn fun i : Fin k => W.special.ordered i.succ
    have hlist : p :: ps = List.ofFn W.special.ordered := by
      exact (List.ofFn_succ (f := W.special.ordered)).symm
    have hinv : ∀ e, e ∈ ((p :: ps).flatMap fun z => z.walk.edges) ↔
        e ∈ W.Q.walk.edgeSet ∧ e ∉ specialCuts hm O hBO := by
      rw [hlist]
      exact W.special.uncutInventory
    constructor
    · intro x y hy hp
      exact native_special_path_keeps_a hm O hBO _ p ps hinv W.special.path
        W.special.edges x y hy (h.keepA x y hy hp)
    · intro x y hy ht hn
      exact native_special_path_keeps_remaining_b hm O hBO _ p ps hinv W.special.path
        W.special.edges x y hy hn (h.keepB x y hy ht)
    · intro e he x hx
      apply native_special_path_c_labels hm O hBO _ h.cLabels p ps hinv ?_
        W.special.path W.special.edges e he x hx
      intro z hz
      rw [hlist] at hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨_, congrArg Subtype.val (W.special.orderedPorts i).2⟩

private theorem outer_edges {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA) :
    W.cycle.edges =
      s(W.base, (W.pieces ⟨(outerFrame F A u hbase).base.length - 1, by
        simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩).finish) ::
      (chainEdges (W.pieces ⟨0, by
        simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩)
        (List.ofFn fun i : Fin ((outerFrame F A u hbase).base.length - 1) =>
          W.pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse := by
  have he := W.edges
  have hlast : pChildIndex F A u hbase =
      ⟨(outerFrame F A u hbase).base.length - 1, by
        simp only [outerFrame, List.length_append, List.length_singleton]; omega⟩ := by
    apply Fin.ext
    simp only [pChildIndex, outerFrame, List.length_append, List.length_singleton, Fin.val_mk]
    omega
  simpa only [hlast] using he

private theorem state_parent_retention {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hk : 2 ≤ k)
    (A : List (Fin (m + 1))) (u : Fin (m + 1))
    (hbase : F.base = A ++ [u]) (hA : 3 ≤ A.length)
    (W : OuterStateParentFor hm F hk A u hbase hA) :
    (∀ (x y : {z : Configuration m // ParentDomain (outerFrame F A u hbase) z}),
      y.val = x.val * a m →
      s(x.val (Fin.last m), y.val (Fin.last m)) ≠ s(protectedP F hk, protectedQ F hk) →
      s(x, y) ∈ W.cycle.edges) ∧
    (∀ (x y : {z : Configuration m // ParentDomain (outerFrame F A u hbase) z}),
      y.val = x.val * b m → x.val (Fin.last m) ∉ insert u F.selected.toFinset →
      s(x, y) ∈ W.cycle.edges) ∧
    (∀ x : Configuration m, s(x, x * c m) ∈ W.cycle.edges.map (Sym2.map Subtype.val) →
      x (Fin.last m) ∈ insert u F.selected.toFinset) := by
  let O := outerFrame F A u hbase
  let hBO := outer_base_bound F A u hbase hA
  have hi := outer_opened_invariants hm F hk A u hbase hA W
  have he := outer_edges hm F hk A u hbase hA W
  refine ⟨?_, ?_, ?_⟩
  · intro x y hy hp
    have hr := native_parent_cycle_keeps_protected_a O hBO (protectedP F hk)
      (protectedQ F hk) W.paths (fun j => (hi j).keepA)
      W.pieces W.childPieces W.cycle he x y hy hp
    obtain ⟨e, he, hmap⟩ := List.mem_map.mp hr
    have heq : e = s(x, y) := (Sym2.map.injective Subtype.val_injective) hmap
    exact heq ▸ he
  · intro x y hy ht
    have hr := native_parent_cycle_keeps_remaining_b O hBO W.paths (fun j => (hi j).keepB)
      W.pieces W.childPieces W.cycle he x y hy ht
    obtain ⟨e, he, hmap⟩ := List.mem_map.mp hr
    have heq : e = s(x, y) := (Sym2.map.injective Subtype.val_injective) hmap
    exact heq ▸ he
  · intro x hx
    exact native_parent_cycle_c_labels hm O hBO W.paths (fun j => (hi j).cLabels)
      W.pieces W.childPieces W.baseCoordinate W.cycle he x hx

#print axioms state_parent_retention

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
