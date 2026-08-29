/- GID: D5/S3/Observer/Bridges/WormholeKernelTransport
   generality: G
   mirror-B: D5/B/S3/Observer/Bridges/WormholeKernelTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Wormhole composition records exact observer-kernel loss. -/

import D5.S3.Observer.Bridges.WormholeCategory
import Mathlib.Data.Setoid.Basic

/-!
A semiconjugate bridge may preserve dynamics while forgetting state
distinctions.  This module isolates that information loss at the level of
`Setoid.ker`.

The first bridge determines the visible state in an intermediate world.
Postcomposing with another bridge can only enlarge the source observer kernel.
Equality is recovered under injectivity of the outer bridge, and an explicit
collapsed pair witnesses strict growth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Bridges.WormholeKernelTransport

open D5.S3.Observer.Bridges.WormholeCategory
open D5.S3.Observer.Bridges.WormholeCategory.Wormhole

universe u v w

variable {source : DynamicalWorld.{u}}
variable {middle : DynamicalWorld.{v}}
variable {target : DynamicalWorld.{w}}

/-- The observation kernel of a wormhole is forward-invariant under the source
dynamics. -/
theorem kernel_forward_invariant
    (bridge : Wormhole source target)
    {first second : source.State}
    (sameVisible : Setoid.ker bridge.map first second) :
    Setoid.ker bridge.map
      (source.step first) (source.step second) := by
  exact observation_fiber_forward_invariant bridge.semiconj sameVisible

/-- Postcomposing a wormhole can only enlarge its source observer kernel. -/
theorem kernel_le_composite
    (first : Wormhole source middle)
    (second : Wormhole middle target) :
    Setoid.ker first.map ≤
      Setoid.ker (compose second first).map := by
  intro left right sameIntermediate
  exact congrArg second.map sameIntermediate

/-- An injective outer wormhole preserves the source observer kernel exactly. -/
theorem kernel_eq_composite_of_outer_injective
    (first : Wormhole source middle)
    (second : Wormhole middle target)
    (outerInjective : Function.Injective second.map) :
    Setoid.ker (compose second first).map =
      Setoid.ker first.map := by
  apply le_antisymm
  · intro left right sameComposite
    exact outerInjective sameComposite
  · exact kernel_le_composite first second

/-- A pair visible after the first bridge but collapsed by the second bridge
witnesses strict growth of the composite kernel. -/
theorem strict_kernel_growth_of_outer_collision
    (first : Wormhole source middle)
    (second : Wormhole middle target)
    {left right : source.State}
    (firstSeparates : first.map left ≠ first.map right)
    (secondCollapses :
      second.map (first.map left) = second.map (first.map right)) :
    Setoid.ker first.map <
      Setoid.ker (compose second first).map := by
  constructor
  · exact kernel_le_composite first second
  · intro reverseInclusion
    have compositeCollision :
        Setoid.ker (compose second first).map left right := by
      exact secondCollapses
    exact firstSeparates (reverseInclusion compositeCollision)

/-- Strict information loss through a composite refutes injectivity of the
outer bridge. -/
theorem strict_growth_refutes_outer_injectivity
    (first : Wormhole source middle)
    (second : Wormhole middle target)
    (strictGrowth :
      Setoid.ker first.map <
        Setoid.ker (compose second first).map) :
    ¬ Function.Injective second.map := by
  intro outerInjective
  have kernelEquality :=
    kernel_eq_composite_of_outer_injective first second outerInjective
  exact (ne_of_lt strictGrowth) kernelEquality.symm

#print axioms kernel_forward_invariant
#print axioms kernel_le_composite
#print axioms kernel_eq_composite_of_outer_injective
#print axioms strict_kernel_growth_of_outer_collision
#print axioms strict_growth_refutes_outer_injectivity

end D5.S3.Observer.Bridges.WormholeKernelTransport
