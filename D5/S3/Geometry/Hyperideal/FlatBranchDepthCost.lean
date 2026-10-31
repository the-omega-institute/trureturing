/- GID: D5/S3/Geometry/Hyperideal/FlatBranchDepthCost
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FlatBranchDepthCost
   mirror-E: none(waiver:universal-real-inequality)
   anchors: []
   utility: none
   digest: A complete binary expansion of positive flat-candidate inequalities has an explicit depth cost. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FlatBranchDepthCost

/-- A finite dependency expansion.  Leaves are counted with multiplicity. -/
inductive DependencyTree (Q : Type*) where
  | leaf : Q → DependencyTree Q
  | branch : Q → DependencyTree Q → DependencyTree Q → DependencyTree Q

def root {Q : Type*} : DependencyTree Q → Q
  | .leaf q => q
  | .branch q _ _ => q

def height {Q : Type*} : DependencyTree Q → ℕ
  | .leaf _ => 0
  | .branch _ left right => max (height left) (height right) + 1

/-- The leaf contribution, retaining repeated leaves as repeated summands. -/
def leafTotal {Q : Type*} (z : Q → ℝ) : DependencyTree Q → ℝ
  | .leaf q => z q
  | .branch _ left right => leafTotal z left + leafTotal z right

/-- Every branch is one instance of the two-child candidate inequality. -/
def Admissible {Q : Type*} (candidate : Q → Q → Q → Prop) :
    DependencyTree Q → Prop
  | .leaf _ => True
  | .branch q left right =>
      candidate q (root left) (root right) ∧
        Admissible candidate left ∧ Admissible candidate right

/-- A complete expansion has equal depth below every branch. -/
def Complete {Q : Type*} : DependencyTree Q → Prop
  | .leaf _ => True
  | .branch _ left right =>
      height left = height right ∧ Complete left ∧ Complete right

private theorem complete_height {Q : Type*} (q : Q)
    (left right : DependencyTree Q) (h : height left = height right) :
    height (.branch q left right) = height left + 1 := by
  simp [height, h]

private theorem complete_leaf_total_gt {Q : Type*}
    (z : Q → ℝ) (hpositive : ∀ q, 1 < z q)
    (tree : DependencyTree Q) (hcomplete : Complete tree) :
    (2 : ℝ) ^ height tree < leafTotal z tree := by
  induction tree with
  | leaf q =>
      simpa [height, leafTotal] using hpositive q
  | branch q left right ihLeft ihRight =>
      rcases hcomplete with ⟨heq, hleft, hright⟩
      have hleft' := ihLeft hleft
      have hright' := ihRight hright
      rw [← heq] at hright'
      have hh := complete_height q left right heq
      rw [hh, pow_succ]
      simp only [leafTotal]
      nlinarith

/-- Exact expansion cost: a full depth-`h` binary tree has `2^h-1` branch
cost units in addition to the repeated leaf values. -/
theorem full_binary_lower_bound {Q : Type*}
    (z : Q → ℝ) (candidate : Q → Q → Q → Prop)
    (hstep : ∀ {q a b}, candidate q a b → z q ≥ 1 + z a + z b)
    (tree : DependencyTree Q) (hcomplete : Complete tree)
    (hadmissible : Admissible candidate tree) :
    z (root tree) ≥
      ((2 : ℝ) ^ height tree - 1) + leafTotal z tree := by
  induction tree with
  | leaf q =>
      simp [root, height, leafTotal]
  | branch q left right ihLeft ihRight =>
      rcases hcomplete with ⟨heq, hleft, hright⟩
      rcases hadmissible with ⟨hc, hleftA, hrightA⟩
      have hl := ihLeft hleft hleftA
      have hr := ihRight hright hrightA
      have hh := complete_height q left right heq
      rw [hh, leafTotal]
      calc
        z q ≥ 1 + z (root left) + z (root right) := hstep hc
        _ ≥ 1 + ((2 : ℝ) ^ height left - 1 + leafTotal z left) +
              ((2 : ℝ) ^ height right - 1 + leafTotal z right) := by
                linarith
        _ = ((2 : ℝ) ^ (height left + 1) - 1) +
              (leafTotal z left + leafTotal z right) := by
                rw [heq, pow_succ]
                ring

/-- The positive leaves make the depth cost strict. -/
theorem full_binary_strict_bound {Q : Type*}
    (z : Q → ℝ) (candidate : Q → Q → Q → Prop)
    (hpositive : ∀ q, 1 < z q)
    (hstep : ∀ {q a b}, candidate q a b → z q ≥ 1 + z a + z b)
    (tree : DependencyTree Q) (hcomplete : Complete tree)
    (hadmissible : Admissible candidate tree) :
    (2 : ℝ) ^ (height tree + 1) - 1 < z (root tree) := by
  have hbound := full_binary_lower_bound z candidate hstep tree hcomplete hadmissible
  have hleaves := complete_leaf_total_gt z hpositive tree hcomplete
  have hp : (2 : ℝ) ^ (height tree + 1) =
      2 * (2 : ℝ) ^ height tree := by
    rw [pow_succ]
    ring
  nlinarith

#print axioms full_binary_lower_bound
#print axioms full_binary_strict_bound

end D5.S3.Geometry.Hyperideal.FlatBranchDepthCost
