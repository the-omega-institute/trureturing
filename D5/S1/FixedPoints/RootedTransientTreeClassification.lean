/- GID: D5/S1/FixedPoints/RootedTransientTreeClassification
   generality: G
   mirror-B: D5/B/S1/FixedPoints/RootedTransientTreeClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recursive branch codes classify finite transient rooted in-trees. -/

/- Library-search audit trail (2026-08-23):
   * Repository searches for rooted trees, branch codes, child-code multisets, W-types, and
     functional-graph isomorphisms found no equal or stronger declaration.
   * Pinned Mathlib has order-theoretic rooted trees and finitely branching W-types, but no
     unordered finite-tree classification theorem. Its `periodicPts`, finite acyclic-relation
     well-foundedness, `Multiset.Rel`, multiset encoding, and well-founded fixpoint equation are
     applied directly below.
   * Searches for an exact hereditary finite-multiset classifier in the pinned library missed.
-/

import Mathlib.Data.Multiset.Fintype
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Logic.Equiv.Multiset

namespace D5.S1.FixedPoints.RootedTransientTreeClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- A child is a nonperiodic state mapped to its parent by the source update. -/
def TransientChild {Y : Type*} (update : Y -> Y) (child parent : Y) : Prop :=
  child ∉ Function.periodicPts update ∧ update child = parent

private theorem transitive_child_iterate {Y : Type*} {update : Y -> Y} {first last : Y}
    (path : Relation.TransGen (TransientChild update) first last) :
    ∃ steps : Nat, 0 < steps ∧ (update^[steps]) first = last := by
  induction path with
  | single edge =>
      exact ⟨1, Nat.zero_lt_succ 0, by simpa using edge.2⟩
  | tail _ edge ih =>
      obtain ⟨steps, positive, reaches⟩ := ih
      refine ⟨steps.succ, Nat.succ_pos steps, ?_⟩
      rw [Function.iterate_succ_apply', reaches, edge.2]

private theorem transitive_child_not_periodic
    {Y : Type*} {update : Y -> Y} {first last : Y}
    (path : Relation.TransGen (TransientChild update) first last) :
    first ∉ Function.periodicPts update := by
  induction path with
  | single edge => exact edge.1
  | tail _ _ ih => exact ih

/-- The nonperiodic-child relation of a finite self-map is well-founded. -/
theorem transient_child_well_founded {Y : Type*} [Finite Y] (update : Y -> Y) :
    WellFounded (TransientChild update) := by
  let closure := Relation.TransGen (TransientChild update)
  have closure_irrefl : ∀ point : Y, ¬ closure point point := by
    intro point cycle
    apply transitive_child_not_periodic cycle
    obtain ⟨steps, positive, fixed⟩ := transitive_child_iterate cycle
    exact Function.mem_periodicPts.mpr ⟨steps, positive, fixed⟩
  letI : Std.Irrefl closure := ⟨closure_irrefl⟩
  have closure_well_founded : WellFounded closure :=
    Finite.wellFounded_of_trans_of_irrefl closure
  exact Subrelation.wf (fun edge => Relation.TransGen.single edge) closure_well_founded

/-- The multiset of actual nonperiodic children, with each element carrying its source edge. -/
noncomputable def transientChildren {Y : Type*} [Fintype Y]
    (update : Y -> Y) (parent : Y) : Multiset {child // TransientChild update child parent} := by
  classical
  exact Finset.univ.val

/-- The hereditary child multiset encoded injectively at every recursive level. -/
noncomputable def branchCode {Y : Type*} [Fintype Y]
    (update : Y -> Y) : Y -> Nat :=
  (transient_child_well_founded update).fix fun parent recurse =>
    Encodable.encode <|
      (transientChildren update parent).map fun child => recurse child.1 child.2

@[simp]
theorem branch_code_eq {Y : Type*} [Fintype Y] (update : Y -> Y) (parent : Y) :
    branchCode update parent =
      Encodable.encode
        ((transientChildren update parent).map (branchCode update ∘ Subtype.val)) := by
  rw [branchCode, WellFounded.fix_eq]
  rfl

/-- Rooted transient in-trees are isomorphic when their children admit a one-to-one recursive
matching. This definition uses only the two source updates and their nonperiodic child edges. -/
noncomputable def RootedTransientTreeIsomorphic
    {Y Z : Type*} [Fintype Y] [Fintype Z] (updateY : Y -> Y) (updateZ : Z -> Z) :
    Y -> Z -> Prop :=
  (transient_child_well_founded updateY).fix fun rootY recurse rootZ =>
    Multiset.Rel
      (fun childY childZ => recurse childY.1 childY.2 childZ.1)
      (transientChildren updateY rootY)
      (transientChildren updateZ rootZ)

@[simp]
theorem rooted_transient_tree_isomorphic_eq
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (updateY : Y -> Y) (updateZ : Z -> Z) (rootY : Y) (rootZ : Z) :
    RootedTransientTreeIsomorphic updateY updateZ rootY rootZ ↔
      Multiset.Rel
        (fun childY childZ =>
          RootedTransientTreeIsomorphic updateY updateZ childY.1 childZ.1)
        (transientChildren updateY rootY)
        (transientChildren updateZ rootZ) := by
  rw [RootedTransientTreeIsomorphic, WellFounded.fix_eq]

/-- Two finite transient rooted in-trees are isomorphic exactly when their recursive branch codes
are equal. -/
theorem rooted_transient_tree_classification
    {Y Z : Type*} [Fintype Y] [Fintype Z]
    (updateY : Y -> Y) (updateZ : Z -> Z) (rootY : Y) (rootZ : Z) :
    RootedTransientTreeIsomorphic updateY updateZ rootY rootZ ↔
      branchCode updateY rootY = branchCode updateZ rootZ := by
  induction rootY using (transient_child_well_founded updateY).induction generalizing rootZ with
  | h rootY inductionHypothesis =>
      rw [rooted_transient_tree_isomorphic_eq, branch_code_eq, branch_code_eq,
        Encodable.encode_inj, ← Multiset.rel_eq, Multiset.rel_map]
      constructor
      · intro matching
        exact matching.mono fun childY _ childZ _ subtreeIso =>
          (inductionHypothesis childY.1 childY.2 childZ.1).mp subtreeIso
      · intro matching
        exact matching.mono fun childY _ childZ _ equalCode =>
          (inductionHypothesis childY.1 childY.2 childZ.1).mpr equalCode

end

end D5.S1.FixedPoints.RootedTransientTreeClassification
