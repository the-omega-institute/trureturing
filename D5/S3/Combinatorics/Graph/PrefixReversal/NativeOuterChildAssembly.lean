/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeOuterChildAssembly
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeOuterChildAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent native child Hamilton paths earn full parent coverage and one actual parent Hamilton cycle. -/
/- outer assembly candidate.
   Child paths are actual previous-cycle constructions. Complete parent
   coverage is derived from native_child_gap_partition, not a premise. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSpecialBoundaryInstances
import Mathlib.Data.List.Count

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveSupply
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.InsertionLayerPartition
open D5.S3.Combinatorics.Graph.Walks.EdgeSlicing
open D5.S3.Combinatorics.Graph.Walks.PathRingSplicing
open private linked_of_getElem finish_eq_last from
  D5.S3.Combinatorics.Graph.Walks.ActualCyclePieceReordering

abbrev ParentDomain {m k : ℕ} (F : SupplyFrame m k) :=
  Layer (insert F.terminal F.selected.toFinset)
    (F.base : Cycle (Fin (m + 1)))

def childStartIndex {m k : ℕ} (F : SupplyFrame m k) (j : Fin F.base.length) : ℕ :=
  if j.val = 0 then 0 else k + j.val

/-- A genuine path on a full independently defined child. The special
path has ends R₀,L_k; ordinary child j has ends R_(k+j),L_(k+j). -/
structure ActualChildPath {m k : ℕ} (F : SupplyFrame m k) (j : Fin F.base.length) where
  piece : Piece (domainGraph (ChildDomain (childGap F j)))
  start_eq : piece.start.val = rightPort F (childStartIndex F j)
  finish_eq : piece.finish.val = leftPort F (k + j.val)
  hamiltonian : piece.walk.IsHamiltonian

private def childLift {m k : ℕ} (F : SupplyFrame m k) (j : Fin F.base.length) :
    domainGraph (ChildDomain (childGap F j)) →g domainGraph (ParentDomain F) :=
  ⟨fun v => ⟨v.val, childDomain_parent (childGap F j) v.property⟩, fun h => h⟩

private theorem childLift_injective {m k : ℕ} (F : SupplyFrame m k)
    (j : Fin F.base.length) : Function.Injective (childLift F j) := by
  intro v w h
  have hv : v.val = w.val :=
    congrArg (fun x : {x : Configuration m // ParentDomain F x} => x.val) h
  exact Subtype.ext hv

private def parentPiece {m k : ℕ} (F : SupplyFrame m k) (j : Fin F.base.length)
    (q : ActualChildPath F j) : Piece (domainGraph (ParentDomain F)) :=
  ⟨childLift F j q.piece.start, childLift F j q.piece.finish,
    q.piece.walk.map (childLift F j)⟩

private theorem parentPiece_domain {m k : ℕ} (F : SupplyFrame m k)
    (j : Fin F.base.length) (q : ActualChildPath F j)
    (v : {x : Configuration m // ParentDomain F x})
    (hv : v ∈ (parentPiece F j q).walk.support) : ChildDomain (childGap F j) v.val := by
  rw [show (parentPiece F j q).walk.support = q.piece.walk.support.map (childLift F j) from
    SimpleGraph.Walk.support_map _ _] at hv
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
  exact (congrArg Subtype.val hu) ▸ u.property

private theorem list_length_le_piece_support {V : Type*} {G : SimpleGraph V}
    (pieces : List (Piece G)) :
    pieces.length ≤ (pieces.flatMap fun z => z.walk.support).length := by
  induction pieces with
  | nil => simp only [List.length_nil, List.flatMap_nil, Nat.le_refl]
  | cons p ps ih =>
    have hpos : 1 ≤ p.walk.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    omega

set_option maxHeartbeats 800000 in
/-- Actual full-child paths, arranged by the native supply order, form one
real parent Hamilton cycle. Disjointness, full support, minimum size and all
connections are proved from the independent domains and native c seams. -/
theorem native_parent_cycle_of_child_paths {m k : ℕ} (hm : 3 ≤ m)
    (F : SupplyFrame m k) (hB : 3 ≤ F.base.length)
    (paths : ∀ j : Fin F.base.length, ActualChildPath F j) :
    ∃ pieces : Fin F.base.length → Piece (domainGraph (ParentDomain F)),
      ∃ base : {x : Configuration m // ParentDomain F x},
      ∃ c : (domainGraph (ParentDomain F)).Walk base base,
      (∀ j, pieces j = parentPiece F j (paths j)) ∧
      base.val = rightPort F 0 ∧ c.IsHamiltonianCycle ∧
      c.support.tail = ((List.ofFn pieces).flatMap fun z => z.walk.support).reverse ∧
      c.edges = s(base, (pieces ⟨F.base.length - 1, by omega⟩).finish) ::
        (chainEdges (pieces ⟨0, by omega⟩)
          (List.ofFn fun i : Fin (F.base.length - 1) =>
            pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩)).reverse := by
  classical
  letI : BEq {x : Configuration m // ParentDomain F x} := instBEqOfDecidableEq
  let pieces (j : Fin F.base.length) := parentPiece F j (paths j)
  let p := pieces ⟨0, by omega⟩
  let ps := List.ofFn fun i : Fin (F.base.length - 1) =>
    pieces ⟨i.val + 1, by have hi := i.isLt; omega⟩
  have hlist : p :: ps = List.ofFn pieces := by
    apply List.ext_getElem
    · simp only [ps, List.length_cons, List.length_ofFn]
      omega
    · intro i hi hj
      cases i with
      | zero => simp only [p, List.getElem_cons_zero, List.getElem_ofFn]
      | succ i => simp only [ps, List.getElem_cons_succ, List.getElem_ofFn]
  have hstart (j : Fin F.base.length) : (pieces j).start.val =
      rightPort F (childStartIndex F j) := (paths j).start_eq
  have hfinish (j : Fin F.base.length) : (pieces j).finish.val =
      leftPort F (k + j.val) := (paths j).finish_eq
  have hdisjoint (i j : Fin F.base.length) (hne : i ≠ j) :
      List.Disjoint (pieces i).walk.support (pieces j).walk.support := by
    apply List.disjoint_left.mpr
    intro v hi hj
    have hdi := parentPiece_domain F i (paths i) v hi
    have hdj := parentPiece_domain F j (paths j) v hj
    obtain ⟨r, _, huniq⟩ := (native_child_gap_partition F hB v.val).mp v.property
    exact hne ((huniq i hdi).trans (huniq j hdj).symm)
  have hn : ((List.ofFn pieces).flatMap fun z => z.walk.support).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
      exact ((paths j).hamiltonian.isPath.map (childLift_injective F j)).support_nodup
    · rw [List.ofFn_eq_map, List.pairwise_map]
      exact (List.nodup_finRange F.base.length).imp (fun {i j} hne => hdisjoint i j hne)
  have hfull : ∀ v : {x : Configuration m // ParentDomain F x},
      ((p :: ps).flatMap fun z => z.walk.support).count v = 1 := by
    intro v
    rw [hlist]
    apply List.count_eq_one_of_mem hn
    obtain ⟨j, hj, _⟩ := (native_child_gap_partition F hB v.val).mp v.property
    let u : {x : Configuration m // ChildDomain (childGap F j) x} := ⟨v.val, hj⟩
    have hu : u ∈ (paths j).piece.walk.support := (paths j).hamiltonian.mem_support u
    apply List.mem_flatMap.mpr
    refine ⟨pieces j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    rw [show (pieces j).walk.support =
      (paths j).piece.walk.support.map (childLift F j) from SimpleGraph.Walk.support_map _ _]
    exact List.mem_map.mpr ⟨u, hu, Subtype.ext rfl⟩
  have hlinked : Linked p ps := by
    apply linked_of_getElem
    intro i hi
    simp only [hlist, List.length_ofFn] at hi
    simp only [hlist]
    simp only [List.getElem_ofFn]
    change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
      (pieces ⟨i, by omega⟩).finish.val (pieces ⟨i + 1, hi⟩).start.val
    rw [hfinish ⟨i, by omega⟩, hstart ⟨i + 1, hi⟩]
    simp only [childStartIndex, Fin.val_mk, if_neg (by omega : ¬ i + 1 = 0)]
    simpa only [Nat.add_assoc] using
      ((native_anchored_supply_coordinates hm F).1 (k + i)).2.2.2
  have hlast : finish p ps = (pieces ⟨F.base.length - 1, by omega⟩).finish := by
    simpa only [hlist, List.getLast_ofFn] using finish_eq_last p ps
  have hclose : (domainGraph (ParentDomain F)).Adj (finish p ps) p.start := by
    rw [hlast]
    change (SimpleGraph.mulCayley ({a m, b m, c m} : Set (Configuration m))).Adj
      (pieces ⟨F.base.length - 1, by omega⟩).finish.val (pieces ⟨0, by omega⟩).start.val
    rw [hfinish, hstart]
    simp only [childStartIndex, Fin.val_mk, if_pos rfl]
    have hp := F.prefix_length
    simp only [List.length_append, F.selected_length] at hp
    rw [show k + (F.base.length - 1) = m - 1 by omega]
    exact (native_anchored_supply_coordinates hm F).2.2
  have hsize : 3 ≤ ((p :: ps).flatMap fun z => z.walk.support).length := by
    rw [hlist]
    have h := list_length_le_piece_support (p :: ps)
    rw [hlist, List.length_ofFn] at h
    omega
  obtain ⟨c, hc, hs, he⟩ := exists_spliced_hamiltonian_cycle p ps hlinked hclose hfull hsize
  refine ⟨pieces, p.start, c, (fun _ => rfl), ?_, hc, ?_, ?_⟩
  · simpa only [p, childStartIndex, Fin.val_mk, ↓reduceIte] using hstart ⟨0, by omega⟩
  · simpa only [hlist] using hs
  · simpa only [hlast, p, ps] using he

#print axioms native_parent_cycle_of_child_paths

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeRecursiveExpansion
