/- GID: D5/S0/History/Spacetime/CompleteBinaryTreeRootTime
   generality: G
   mirror-B: D5/B/S0/History/Spacetime/CompleteBinaryTreeRootTime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The root time of a finite complete binary tree is the maximum leaf time plus leaf depth. -/

import Mathlib.Data.Int.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.WithTop

namespace D5.S0.History.Spacetime.CompleteBinaryTreeRootTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A finite complete binary tree whose leaves carry integer input times. -/
inductive CompleteBinaryTree where
  | leaf (time : ℤ)
  | node (left right : CompleteBinaryTree)

/-- The default recursively computed time at the root. -/
def rootTime : CompleteBinaryTree → ℤ
  | .leaf time => time
  | .node left right => max (rootTime left) (rootTime right) + 1

/-- A leaf record carries its input time and its depth from the current root. -/
def bumpDepth (record : ℤ × ℕ) : ℤ × ℕ := (record.1, record.2 + 1)

/-- The finite leaf records, with one depth increment for each traversed edge. -/
def leafData : CompleteBinaryTree → List (ℤ × ℕ)
  | .leaf time => [(time, 0)]
  | .node left right =>
      (leafData left).map bumpDepth ++ (leafData right).map bumpDepth

/-- The finite list of values `time + depth` for all leaves. -/
def leafScore (record : ℤ × ℕ) : ℤ := record.1 + (record.2 : ℤ)

def leafScores (tree : CompleteBinaryTree) : List ℤ :=
  (leafData tree).map leafScore

private lemma maximum_map_add (values : List ℤ) (offset : ℤ) :
    (values.map (· + offset)).maximum = values.maximum + offset := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.maximum_cons, ih]
      cases h : tail.maximum with
      | bot => simp [h]
      | coe maximumTail =>
          simp only [h, WithBot.coe_add]
          have h' : max (head + offset) (maximumTail + offset) =
              max head maximumTail + offset := by
            simpa [add_comm] using (max_add_add_left offset head maximumTail)
          exact_mod_cast h'

private lemma map_bumpDepth_leafScore (records : List (ℤ × ℕ)) :
    (records.map bumpDepth).map leafScore =
      (records.map leafScore).map (· + 1) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro record _
  rcases record with ⟨time, depth⟩
  simp [bumpDepth, leafScore, Nat.cast_add, add_assoc, add_comm, add_left_comm]
  omega

/-- For every finite complete binary tree, recursively computed root time equals
    the maximum of `leaf time + depth` over its finite leaves. -/
theorem rootTime_eq_max_leaf_time_add_depth : ∀ tree : CompleteBinaryTree,
    (rootTime tree : WithBot ℤ) = (leafScores tree).maximum
  | .leaf time => by
      simp [rootTime, leafScores, leafData, leafScore]
  | .node left right => by
      change ((max (rootTime left) (rootTime right) + 1 : ℤ) : WithBot ℤ) =
        (((leafData left).map bumpDepth ++ (leafData right).map bumpDepth).map leafScore).maximum
      simp only [List.map_append, List.maximum_append]
      rw [map_bumpDepth_leafScore, map_bumpDepth_leafScore]
      rw [maximum_map_add, maximum_map_add]
      have leftEquation := rootTime_eq_max_leaf_time_add_depth left
      have rightEquation := rootTime_eq_max_leaf_time_add_depth right
      change ((max (rootTime left) (rootTime right) + 1 : ℤ) : WithBot ℤ) =
        max ((leafScores left).maximum + (1 : WithBot ℤ))
          ((leafScores right).maximum + (1 : WithBot ℤ))
      rw [← leftEquation, ← rightEquation]
      have rootReassociation : max (rootTime left) (rootTime right) + 1 =
          max (rootTime left + 1) (rootTime right + 1) := by
        simpa [add_comm] using
          (max_add_add_left (1 : ℤ) (rootTime left) (rootTime right)).symm
      exact_mod_cast rootReassociation

#print axioms rootTime_eq_max_leaf_time_add_depth

end D5.S0.History.Spacetime.CompleteBinaryTreeRootTime
