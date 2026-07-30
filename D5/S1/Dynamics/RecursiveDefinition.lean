/- GID: D5/S1/Dynamics/RecursiveDefinition
   generality: G
   mirror-B: D5/B/S1/Dynamics/RecursiveDefinition
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Recursive definitions are fixed points with explicit extremal selections. -/

import D5.S1.Dynamics.KnasterTarski

namespace D5.S1.Dynamics.RecursiveDefinition

open Function (fixedPoints)

/-- The two extremal interpretations of a monotone definition operator. -/
inductive ExtremalFixedPointSelection
  | least
  | greatest

/-- Evaluate an explicit extremal fixed-point selection. -/
def selectExtremalFixedPoint
    {α : Type*} [CompleteLattice α] (f : α →o α) :
    ExtremalFixedPointSelection → α
  | .least => f.lfp
  | .greatest => f.gfp

/-- Solving a recursive equation is exactly being a fixed point of its
definition operator. -/
theorem is_recursive_definition_iff_fixed_point
    {α : Type*} (f : α → α) (x : α) :
    f x = x ↔ x ∈ fixedPoints f :=
  Iff.rfl

/-- If the least and greatest fixed points differ, the explicit extremal
selections yield fixed points with different values. -/
theorem extremal_selection_distinguishes_fixed_points
    {α : Type*} [CompleteLattice α] (f : α →o α)
    (hDistinct : f.lfp ≠ f.gfp) :
    f (selectExtremalFixedPoint f .least) =
        selectExtremalFixedPoint f .least ∧
      f (selectExtremalFixedPoint f .greatest) =
        selectExtremalFixedPoint f .greatest ∧
      selectExtremalFixedPoint f .least ≠
        selectExtremalFixedPoint f .greatest := by
  exact ⟨f.map_lfp, f.map_gfp, hDistinct⟩

/-- A unique fixed point forces the least and greatest fixed points to
coincide. -/
theorem unique_fixed_point_implies_lfp_eq_gfp
    {α : Type*} [CompleteLattice α] (f : α →o α)
    (hUnique : ∃! x, f x = x) :
    f.lfp = f.gfp := by
  obtain ⟨x, _hx, hUniqueAt⟩ := hUnique
  exact (hUniqueAt f.lfp f.map_lfp).trans
    (hUniqueAt f.gfp f.map_gfp).symm

end D5.S1.Dynamics.RecursiveDefinition
