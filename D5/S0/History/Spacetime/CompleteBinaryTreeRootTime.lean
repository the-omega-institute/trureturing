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
import OmegaMath.Data.Int

/-! Root times of complete binary trees with unit edge delays. -/

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

/-- A complete binary tree with leaf times in the strict integer representation. -/
inductive StrictCompleteBinaryTree where
  | leaf (time : Omega.Int)
  | node (left right : StrictCompleteBinaryTree)

/-- Compute a strict root time by adding one at each internal node. -/
noncomputable def strictRootTime : StrictCompleteBinaryTree → Omega.Int :=
  StrictCompleteBinaryTree.rec (fun time => time)
    (fun _ _ left right => (Omega.Int.max left right).add Omega.Int.one)

/-- Take the maximum of input time plus depth over the leaves, starting at `depth`. -/
noncomputable def strictLeafMaximumFrom (tree : StrictCompleteBinaryTree) :
    Omega.Nat → Omega.Int :=
  StrictCompleteBinaryTree.rec (motive := fun _ => Omega.Nat → Omega.Int)
    (fun time depth => time.add (.ofNat depth))
    (fun _ _ left right depth => Omega.Int.max (left depth.succ) (right depth.succ)) tree

private theorem map_bumpDepth_leafScore (time : Omega.Int) (depth : Omega.Nat) :
    Omega.Eq (time.add (.ofNat depth.succ)) ((time.add Omega.Int.one).add (.ofNat depth)) :=
  (Omega.congrArg time.add (Omega.Int.add_comm (.ofNat depth) Omega.Int.one)).trans
    (Omega.Int.add_assoc time Omega.Int.one (.ofNat depth)).symm

private theorem maximum_map_add (tree : StrictCompleteBinaryTree) :
    ∀ depth, Omega.Eq (strictLeafMaximumFrom tree depth)
      ((strictRootTime tree).add (.ofNat depth)) :=
  StrictCompleteBinaryTree.rec (motive := fun tree => ∀ depth,
    Omega.Eq (strictLeafMaximumFrom tree depth) ((strictRootTime tree).add (.ofNat depth)))
    (fun _ _ => Omega.Eq.refl)
    (fun left right leftAgreement rightAgreement depth =>
      let leftTime := strictRootTime left
      let rightTime := strictRootTime right
      (Omega.Eq.map₂ Omega.Int.max (leftAgreement depth.succ) (rightAgreement depth.succ)).trans
        ((Omega.Int.max_add_right leftTime rightTime (.ofNat depth.succ)).trans
          (map_bumpDepth_leafScore (Omega.Int.max leftTime rightTime) depth)))
    tree

/-- The recursively computed root time is the maximum of input time plus depth over the leaves. -/
theorem rootTime_eq_max_leaf_time_add_depth (tree : StrictCompleteBinaryTree) :
    Omega.Eq (strictRootTime tree) (strictLeafMaximumFrom tree .zero) :=
  (Omega.Int.add_zero (strictRootTime tree)).symm.trans (maximum_map_add tree .zero).symm

end D5.S0.History.Spacetime.CompleteBinaryTreeRootTime
