/- GID: D5/S0/Certificates/TreeBottomPinnacleNonunique
   generality: I
   mirror-B: D5/B/S0/Certificates/TreeBottomPinnacleNonunique
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=bounded-enumeration; basis=terminal=gid:D5/S0/Certificates/TreeBottomPinnacleNonunique.tree_no_minimum
   digest: A six-vertex tree has two bottom size-three pinnacle sets. -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.TreeBottomPinnacleNonunique

set_option maxRecDepth 100000

private def adjacent (vertex neighbor : Fin 6) : Prop :=
  (vertex = 1 ∧ neighbor ∈ ([0, 2, 3, 4] : List (Fin 6))) ∨
  (neighbor = 1 ∧ vertex ∈ ([0, 2, 3, 4] : List (Fin 6))) ∨
  (vertex = 2 ∧ neighbor = 5) ∨ (vertex = 5 ∧ neighbor = 2)

/-- The tree with edges 01, 12, 13, 14, and 25. -/
def tree : SimpleGraph (Fin 6) where
  Adj := adjacent
  symm := ⟨by unfold adjacent; decide⟩
  loopless := ⟨by unfold adjacent; decide⟩

instance treeAdjDecidable : DecidableRel tree.Adj :=
  fun _ _ => by unfold tree adjacent; infer_instance

theorem tree_isTree : tree.IsTree := by
  have reach (vertex : Fin 6) : tree.Reachable 1 vertex := by
    fin_cases vertex
    · exact (show tree.Adj 1 0 from by decide).reachable
    · exact SimpleGraph.Reachable.refl _
    · exact (show tree.Adj 1 2 from by decide).reachable
    · exact (show tree.Adj 1 3 from by decide).reachable
    · exact (show tree.Adj 1 4 from by decide).reachable
    · exact (show tree.Adj 1 2 from by decide).reachable.trans
        (show tree.Adj 2 5 from by decide).reachable
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨⟨fun vertex neighbor => (reach vertex).symm.trans (reach neighbor)⟩, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  decide

/-- Labels are one-based: a bijection to `Fin 6` supplies the labels 1 through 6. -/
def pinnacleSet (label : Fin 6 → Fin 6) : Finset Nat :=
  (Finset.univ.filter fun vertex =>
    ∀ neighbor, tree.Adj vertex neighbor → label neighbor < label vertex).image
      (fun vertex => (label vertex).val + 1)

/-- Attainability uses every bijective labeling, not merely the exhibited witnesses. -/
def Attainable (pinnacles : Finset Nat) : Prop :=
  ∃ label : Fin 6 → Fin 6, Function.Bijective label ∧ pinnacleSet label = pinnacles

/-- Coordinatewise comparison of increasingly sorted pinnacle sets. -/
def CoordinateLE (left right : Finset Nat) : Prop :=
  List.Forall₂ (· ≤ ·) (left.sort (· ≤ ·)) (right.sort (· ≤ ·))

private def listPinnacles (label : List (Fin 6)) : Finset Nat :=
  pinnacleSet fun vertex => (label[vertex.val]?).getD 0

/-- Kernel reduction checks all 720 permutations using structural recursion. -/
private theorem enumeration :
    (List.finRange 6).permutations'.all (fun label => decide
      ((listPinnacles label).card = 3 →
        listPinnacles label = {2, 5, 6} ∨ listPinnacles label = {3, 4, 6} ∨
        listPinnacles label = {3, 5, 6} ∨ listPinnacles label = {4, 5, 6})) = true := by
  decide +kernel

theorem attainable_three_cases (pinnacles : Finset Nat)
    (attainable : Attainable pinnacles) (size : pinnacles.card = 3) :
    pinnacles = {2, 5, 6} ∨ pinnacles = {3, 4, 6} ∨
      pinnacles = {3, 5, 6} ∨ pinnacles = {4, 5, 6} := by
  obtain ⟨label, bijective, rfl⟩ := attainable
  have member : List.ofFn label ∈ (List.finRange 6).permutations' := by
    apply List.mem_permutations'.mpr
    simpa only [List.ofFn_eq_map, Equiv.coe_ofBijective] using
      (Equiv.Perm.map_finRange_perm (Equiv.ofBijective label bijective))
  have checked := (List.all_eq_true.mp enumeration) (List.ofFn label) member
  have lookup : listPinnacles (List.ofFn label) = pinnacleSet label := by
    unfold listPinnacles
    congr 1
    funext vertex
    fin_cases vertex <;> simp
  rw [decide_eq_true_eq, lookup] at checked
  exact checked size

theorem attainable_256 : Attainable {2, 5, 6} := by
  refine ⟨![2, 3, 0, 4, 5, 1], ?_, ?_⟩ <;> decide

theorem attainable_346 : Attainable {3, 4, 6} := by
  refine ⟨![0, 1, 4, 2, 3, 5], ?_, ?_⟩ <;> decide

/-- A TREE has no minimum size-three pinnacle set, answering the tree question in
Section 6 of Bozeman, Cheng, Harris, Lasinis, and Walker, arXiv:2406.19562v1.
Figure 10 of that paper already exhibits the same two bottom size-three pinnacle
sets {2,5,6} and {3,4,6} in a graph containing cycles. The poset is not claimed to
be new: what is formalized here is its realization by a tree. No classification
or uniqueness claim for other cardinalities is assumed. -/
theorem tree_no_minimum :
    tree.IsTree ∧ ¬ ∃ least : Finset Nat,
      least.card = 3 ∧ Attainable least ∧
        ∀ other : Finset Nat, other.card = 3 → Attainable other →
          CoordinateLE least other := by
  refine ⟨tree_isTree, ?_⟩
  rintro ⟨least, size, attainable, minimum⟩
  have below256 := minimum {2, 5, 6} (by decide) attainable_256
  have below346 := minimum {3, 4, 6} (by decide) attainable_346
  rcases attainable_three_cases least attainable size with rfl | rfl | rfl | rfl
  · norm_num [CoordinateLE, Finset.sort_insert] at below346
  · norm_num [CoordinateLE, Finset.sort_insert] at below256
  · norm_num [CoordinateLE, Finset.sort_insert] at below256
  · norm_num [CoordinateLE, Finset.sort_insert] at below256

#print axioms tree
#print axioms treeAdjDecidable
#print axioms tree_isTree
#print axioms pinnacleSet
#print axioms Attainable
#print axioms CoordinateLE
#print axioms attainable_three_cases
#print axioms attainable_256
#print axioms attainable_346
#print axioms tree_no_minimum

end D5.S0.Certificates.TreeBottomPinnacleNonunique
