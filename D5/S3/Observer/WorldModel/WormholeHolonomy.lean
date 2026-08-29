/- GID: D5/S3/Observer/WorldModel/WormholeHolonomy
   generality: G
   mirror-B: D5/B/S3/Observer/WorldModel/WormholeHolonomy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Round trips through observer wormholes define holonomy, with inverse
     bridges giving the trivial loop. -/

import D5.S3.Observer.Bridges.WormholeCategory

/-!
A pair of opposite observer bridges need not be inverse.  Their composite is a
round-trip endomorphism of the source world.  Its failure to fix a state is the
minimal set-theoretic notion of wormhole holonomy used here.

This module does not identify that notion with differential-geometric
holonomy.  It records only round-trip transport in a typed dynamical network.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.WorldModel.WormholeHolonomy

open D5.S3.Observer.Bridges.WormholeCategory
open D5.S3.Observer.Bridges.WormholeCategory.Wormhole

universe u v

variable {source : DynamicalWorld.{u}}
variable {target : DynamicalWorld.{v}}

/-- The source endomorphism obtained by travelling through a forward bridge
and returning through a backward bridge. -/
def roundTrip
    (forward : Wormhole source target)
    (backward : Wormhole target source) :
    Wormhole source source :=
  compose backward forward

/-- A round trip has holonomy at a state when it fails to return that state. -/
def HasHolonomyAt
    (forward : Wormhole source target)
    (backward : Wormhole target source)
    (state : source.State) : Prop :=
  (roundTrip forward backward).map state ≠ state

/-- Round trips preserve every fixed source state as a fixed state of the
round-trip dynamics. -/
theorem round_trip_maps_fixed_point
    (forward : Wormhole source target)
    (backward : Wormhole target source)
    {state : source.State}
    (fixed : Function.IsFixedPt source.step state) :
    Function.IsFixedPt source.step
      ((roundTrip forward backward).map state) := by
  exact maps_fixed_point (roundTrip forward backward) fixed

/-- A genuine left inverse makes the round trip equal to the identity
wormhole. -/
theorem round_trip_eq_identity_of_left_inverse
    (forward : Wormhole source target)
    (backward : Wormhole target source)
    (leftInverse :
      Function.LeftInverse backward.map forward.map) :
    roundTrip forward backward = identity source := by
  apply Wormhole.ext
  funext state
  exact leftInverse state

/-- A left inverse rules out holonomy at every source state. -/
theorem no_holonomy_of_left_inverse
    (forward : Wormhole source target)
    (backward : Wormhole target source)
    (leftInverse :
      Function.LeftInverse backward.map forward.map)
    (state : source.State) :
    ¬ HasHolonomyAt forward backward state := by
  intro holonomy
  exact holonomy (leftInverse state)

/-- Any holonomy witness refutes the claim that the return bridge is a left
inverse. -/
theorem holonomy_refutes_left_inverse
    (forward : Wormhole source target)
    (backward : Wormhole target source)
    {state : source.State}
    (holonomy : HasHolonomyAt forward backward state) :
    ¬ Function.LeftInverse backward.map forward.map := by
  intro leftInverse
  exact holonomy (leftInverse state)

#print axioms round_trip_maps_fixed_point
#print axioms round_trip_eq_identity_of_left_inverse
#print axioms no_holonomy_of_left_inverse
#print axioms holonomy_refutes_left_inverse

end D5.S3.Observer.WorldModel.WormholeHolonomy
