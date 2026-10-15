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

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeActualStateSuppliers
