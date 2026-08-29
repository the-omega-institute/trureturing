/- GID: D5/S3/Observer/Bridges/FixedPointSemiconjugacy
   generality: G
   mirror-B: D5/B/S3/Observer/Bridges/FixedPointSemiconjugacy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Semiconjugate observer bridges transport fixed points and forward-invariant observation fibers across world models. -/

import Mathlib.Logic.Function.Conjugate
import Mathlib.Logic.Function.Iterate

/-!
A mathematically controlled version of the source's “wormhole” metaphor is a
semiconjugacy.  It transports visible dynamics without asserting that the two
state spaces are ontologically identical.  An injective bridge reflects fixed
points as well as transporting them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Bridges.FixedPointSemiconjugacy

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- A fixed point is transported through every semiconjugate bridge. -/
theorem fixed_point_maps
    {bridge : X → Y} {sourceStep : X → X} {targetStep : Y → Y} {x : X}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hFixed : Function.IsFixedPt sourceStep x) :
    Function.IsFixedPt targetStep (bridge x) := by
  change targetStep (bridge x) = bridge x
  rw [← hSemiconj x, hFixed]

/-- An injective semiconjugate bridge also reflects fixed points. -/
theorem fixed_point_reflects_of_injective
    {bridge : X → Y} {sourceStep : X → X} {targetStep : Y → Y} {x : X}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hInjective : Function.Injective bridge)
    (hFixed : Function.IsFixedPt targetStep (bridge x)) :
    Function.IsFixedPt sourceStep x := by
  apply hInjective
  change bridge (sourceStep x) = bridge x
  rw [hSemiconj x, hFixed]

/-- Under an injective semiconjugacy, fixedness is exactly preserved. -/
theorem fixed_point_iff_of_injective
    {bridge : X → Y} {sourceStep : X → X} {targetStep : Y → Y} {x : X}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (hInjective : Function.Injective bridge) :
    Function.IsFixedPt sourceStep x ↔
      Function.IsFixedPt targetStep (bridge x) := by
  constructor
  · exact fixed_point_maps hSemiconj
  · exact fixed_point_reflects_of_injective hSemiconj hInjective

/-- Equality under the observer remains equal after one semiconjugate step. -/
theorem observation_fiber_forward_invariant
    {bridge : X → Y} {sourceStep : X → X} {targetStep : Y → Y}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    {x₁ x₂ : X} (hVisible : bridge x₁ = bridge x₂) :
    bridge (sourceStep x₁) = bridge (sourceStep x₂) := by
  rw [hSemiconj x₁, hSemiconj x₂, hVisible]

/-- Semiconjugacy transports every finite iterate, not only one step. -/
theorem semiconjugacy_iterate
    {bridge : X → Y} {sourceStep : X → X} {targetStep : Y → Y}
    (hSemiconj : Function.Semiconj bridge sourceStep targetStep)
    (n : ℕ) (x : X) :
    bridge ((sourceStep^[n]) x) = (targetStep^[n]) (bridge x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        hSemiconj, ih]

/-- Fixed-point transport composes along two observer bridges. -/
theorem fixed_point_maps_across_composite
    {firstBridge : X → Y} {secondBridge : Y → Z}
    {firstStep : X → X} {secondStep : Y → Y} {thirdStep : Z → Z}
    {x : X}
    (hFirst : Function.Semiconj firstBridge firstStep secondStep)
    (hSecond : Function.Semiconj secondBridge secondStep thirdStep)
    (hFixed : Function.IsFixedPt firstStep x) :
    Function.IsFixedPt thirdStep ((secondBridge ∘ firstBridge) x) := by
  exact fixed_point_maps (hFirst.trans hSecond) hFixed

#print axioms fixed_point_maps
#print axioms fixed_point_reflects_of_injective
#print axioms fixed_point_iff_of_injective
#print axioms observation_fiber_forward_invariant
#print axioms semiconjugacy_iterate
#print axioms fixed_point_maps_across_composite

end D5.S3.Observer.Bridges.FixedPointSemiconjugacy
