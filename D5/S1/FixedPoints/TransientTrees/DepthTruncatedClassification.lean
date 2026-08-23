/- GID: D5/S1/FixedPoints/TransientTrees/DepthTruncatedClassification
   generality: G
   mirror-B: D5/B/S1/FixedPoints/TransientTrees/DepthTruncatedClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite-depth branch codes classify truncated transient trees and truncate naturally. -/

import D5.S1.FixedPoints.RootedTransientTreeClassification
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-23):
   * Repository exact hit `RootedTransientTreeClassification.TransientChild` supplies the
     canonical nonperiodic predecessor relation, and `transientChildren` supplies its actual
     finite child multiset. Both are imported and used directly below.
   * Pinned Mathlib exact hits `Function.periodicOrbit`, `Cycle`, `Cycle.map`,
     `List.IsRotated`, quotient fintypes, and `Multiset.rel_eq` supply cyclic necklaces,
     component enumeration, and unordered child matching.
   * Repository and pinned-Mathlib searches found no finite-depth unordered-tree classifier or
     natural truncation theorem for the resulting decorated-cycle multiset. -/

namespace D5.S1.FixedPoints.TransientTrees.DepthTruncatedClassification

open D5.S1.FixedPoints.RootedTransientTreeClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- Unordered rooted-tree codes retaining exactly the first `depth` child layers. -/
abbrev DepthBranchCode : Nat -> Type
  | 0 => PUnit
  | depth + 1 => Multiset (DepthBranchCode depth)

/-- The finite-depth rooted-tree relation, constructed from actual nonperiodic predecessors. -/
def TruncatedRootedTreeIsomorphic
    {Y Z : Type*} [Fintype Y] [Fintype Z] (updateY : Y -> Y) (updateZ : Z -> Z) :
    (depth : Nat) -> Y -> Z -> Prop
  | 0, _, _ => True
  | depth + 1, rootY, rootZ =>
      Multiset.Rel
        (fun childY childZ =>
          TruncatedRootedTreeIsomorphic updateY updateZ depth childY.1 childZ.1)
        (transientChildren updateY rootY)
        (transientChildren updateZ rootZ)

/-- The depth code of the actual transient in-tree rooted at `root`. -/
noncomputable def depthBranchCode {Y : Type*} [Fintype Y] (update : Y -> Y) :
    (depth : Nat) -> Y -> DepthBranchCode depth
  | 0, _ => PUnit.unit
  | depth + 1, root =>
      (transientChildren update root).map fun child =>
        depthBranchCode update depth child.1

/-- Removing the last retained layer maps depth `h + 1` codes to depth `h` codes. -/
def truncateBranchCode : (depth : Nat) -> DepthBranchCode (depth + 1) -> DepthBranchCode depth
  | 0, _ => PUnit.unit
  | depth + 1, children => children.map (truncateBranchCode depth)

/-- Periodic roots are identified exactly when Mathlib gives them the same cyclic orbit. -/
def periodicComponentSetoid {Y : Type*} (update : Y -> Y) :
    Setoid {root : Y // root ∈ Function.periodicPts update} :=
  Setoid.ker fun root => Function.periodicOrbit update root.1

/-- A connected component's unique directed cycle, represented without a chosen start point. -/
abbrev PeriodicComponent {Y : Type*} (update : Y -> Y) :=
  Quotient (periodicComponentSetoid update)

/-- Every directed-cycle component, once and with multiplicity across equally decorated cycles. -/
noncomputable def periodicComponents {Y : Type*} [Fintype Y] (update : Y -> Y) :
    Multiset (PeriodicComponent update) := by
  classical
  letI : DecidableRel (periodicComponentSetoid update).r := Classical.decRel _
  letI : Fintype (PeriodicComponent update) := Quotient.fintype (periodicComponentSetoid update)
  exact Finset.univ.val

/-- Decorate a component's cyclic orbit by the depth code at each periodic root. -/
noncomputable def componentDecoration {Y : Type*} [Fintype Y]
    (depth : Nat) (update : Y -> Y) (component : PeriodicComponent update) :
    Cycle (DepthBranchCode depth) :=
  (Function.periodicOrbit update (Quotient.out component).1).map
    (depthBranchCode update depth)

/-- The multiset of all depth-decorated component necklaces of a finite self-map. -/
noncomputable def depthInvariant {Y : Type*} [Fintype Y]
    (depth : Nat) (update : Y -> Y) : Multiset (Cycle (DepthBranchCode depth)) :=
  (periodicComponents update).map (componentDecoration depth update)

/-- Apply the canonical branch-code truncation at every site of every component necklace. -/
def truncateDepthInvariant (depth : Nat) :
    Multiset (Cycle (DepthBranchCode (depth + 1))) ->
      Multiset (Cycle (DepthBranchCode depth)) :=
  Multiset.map (Cycle.map (truncateBranchCode depth))

private theorem cycle_map_map {A B C : Type*} (g : B -> C) (f : A -> B) (cycle : Cycle A) :
    (cycle.map f).map g = cycle.map (g ∘ f) := by
  induction cycle using Cycle.induction_on with
  | nil => rfl
  | cons value entries inductionHypothesis =>
      simp only [Cycle.map_coe, List.map_map]

private theorem cycle_map_congr {A B : Type*} {f g : A -> B}
    (equal : ∀ value, f value = g value) (cycle : Cycle A) :
    cycle.map f = cycle.map g := by
  induction cycle using Cycle.induction_on with
  | nil => rfl
  | cons value entries inductionHypothesis =>
      simp only [Cycle.map_coe]
      exact congrArg (fun list : List B => (list : Cycle B)) <|
        congrArg (fun map => (value :: entries).map map) (funext equal)

@[simp]
theorem truncate_depth_branch_code {Y : Type*} [Fintype Y]
    (update : Y -> Y) (depth : Nat) (root : Y) :
    truncateBranchCode depth (depthBranchCode update (depth + 1) root) =
      depthBranchCode update depth root := by
  induction depth generalizing root with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [depthBranchCode, truncateBranchCode, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro child child_mem
      exact inductionHypothesis child.1

private theorem truncate_depth_invariant {Y : Type*} [Fintype Y]
    (update : Y -> Y) (depth : Nat) :
    truncateDepthInvariant depth (depthInvariant (depth + 1) update) =
      depthInvariant depth update := by
  unfold truncateDepthInvariant depthInvariant componentDecoration
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro component component_mem
  simp only [Function.comp_apply]
  rw [cycle_map_map]
  apply cycle_map_congr
  intro root
  exact truncate_depth_branch_code update depth root

/-- Depth codes are complete invariants of truncated transient rooted trees, and both rooted codes
and decorated component necklaces commute with the named truncation maps. -/
theorem depth_truncated_tree_classification_and_naturality
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (updateY : Y -> Y) (updateZ : Z -> Z) (depth : Nat) :
    (∀ rootY rootZ,
      TruncatedRootedTreeIsomorphic updateY updateZ depth rootY rootZ <->
        depthBranchCode updateY depth rootY = depthBranchCode updateZ depth rootZ) ∧
    (∀ rootY,
      truncateBranchCode depth (depthBranchCode updateY (depth + 1) rootY) =
        depthBranchCode updateY depth rootY) ∧
    truncateDepthInvariant depth (depthInvariant (depth + 1) updateY) =
      depthInvariant depth updateY := by
  constructor
  · intro rootY rootZ
    induction depth generalizing rootY rootZ with
    | zero => simp [TruncatedRootedTreeIsomorphic, depthBranchCode]
    | succ depth inductionHypothesis =>
        rw [TruncatedRootedTreeIsomorphic, depthBranchCode, depthBranchCode,
          ← Multiset.rel_eq, Multiset.rel_map]
        constructor
        · intro matching
          exact matching.mono fun childY _ childZ _ subtreeIso =>
            (inductionHypothesis childY.1 childZ.1).mp subtreeIso
        · intro matching
          exact matching.mono fun childY _ childZ _ equalCode =>
            (inductionHypothesis childY.1 childZ.1).mpr equalCode
  · constructor
    · exact fun rootY => truncate_depth_branch_code updateY depth rootY
    · exact truncate_depth_invariant updateY depth

#print axioms depth_truncated_tree_classification_and_naturality

end

end D5.S1.FixedPoints.TransientTrees.DepthTruncatedClassification
