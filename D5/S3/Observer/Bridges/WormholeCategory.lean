/- GID: D5/S3/Observer/Bridges/WormholeCategory
   generality: G
   mirror-B: D5/B/S3/Observer/Bridges/WormholeCategory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed semiconjugate bridges compose and transport fixed behavior. -/

import D5.S3.Observer.Bridges.FixedPointSemiconjugacy

/-!
The source metaphor of a “wormhole” is formalized here as a typed
semiconjugacy between dynamical worlds.  The structure does not identify the
two state carriers.  It records only a map that intertwines their updates.

Identity and composition are defined explicitly.  The resulting laws are
ordinary equality of bridge structures, using proof irrelevance for the
semiconjugacy field.  No inverse is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Bridges.WormholeCategory

open D5.S3.Observer.Bridges.FixedPointSemiconjugacy

universe u v w z

/-- A typed state carrier equipped with one update map. -/
structure DynamicalWorld where
  State : Type u
  step : State → State

/-- A dynamics-preserving bridge from one world to another. -/
structure Wormhole
    (source : DynamicalWorld.{u}) (target : DynamicalWorld.{v}) where
  map : source.State → target.State
  semiconj : Function.Semiconj map source.step target.step

namespace Wormhole

variable {source : DynamicalWorld.{u}}
variable {middle : DynamicalWorld.{v}}
variable {target : DynamicalWorld.{w}}

/-- Two wormholes are equal when their underlying maps are equal. -/
@[ext] theorem ext
    {first second : Wormhole source target}
    (hMap : first.map = second.map) :
    first = second := by
  cases first with
  | mk firstMap firstSemiconj =>
      cases second with
      | mk secondMap secondSemiconj =>
          dsimp at hMap
          subst secondMap
          rfl

/-- Identity wormhole on one dynamical world. -/
def identity (world : DynamicalWorld.{u}) : Wormhole world world where
  map := id
  semiconj := by
    intro state
    rfl

/-- Compose two consecutive wormholes. -/
def compose
    (second : Wormhole middle target)
    (first : Wormhole source middle) :
    Wormhole source target where
  map := second.map ∘ first.map
  semiconj := first.semiconj.trans second.semiconj

/-- Left identity for wormhole composition. -/
theorem identity_compose (bridge : Wormhole source target) :
    compose (identity target) bridge = bridge := by
  apply ext
  funext state
  rfl

/-- Right identity for wormhole composition. -/
theorem compose_identity (bridge : Wormhole source target) :
    compose bridge (identity source) = bridge := by
  apply ext
  funext state
  rfl

/-- Associativity of wormhole composition. -/
theorem compose_assoc
    {fourth : DynamicalWorld.{z}}
    (third : Wormhole target fourth)
    (second : Wormhole middle target)
    (first : Wormhole source middle) :
    compose third (compose second first) =
      compose (compose third second) first := by
  apply ext
  funext state
  rfl

/-- A wormhole transports every fixed source state to a fixed target state. -/
theorem maps_fixed_point
    (bridge : Wormhole source target) {state : source.State}
    (hFixed : Function.IsFixedPt source.step state) :
    Function.IsFixedPt target.step (bridge.map state) :=
  fixed_point_maps bridge.semiconj hFixed

/-- A wormhole transports every finite iterate of the source dynamics. -/
theorem maps_iterate
    (bridge : Wormhole source target)
    (iteration : ℕ) (state : source.State) :
    bridge.map ((source.step^[iteration]) state) =
      (target.step^[iteration]) (bridge.map state) :=
  semiconjugacy_iterate bridge.semiconj iteration state

/-- Composite wormholes transport fixed points across multiple worlds. -/
theorem composite_maps_fixed_point
    (second : Wormhole middle target)
    (first : Wormhole source middle)
    {state : source.State}
    (hFixed : Function.IsFixedPt source.step state) :
    Function.IsFixedPt target.step
      ((compose second first).map state) :=
  maps_fixed_point (compose second first) hFixed

#print axioms Wormhole.ext
#print axioms identity_compose
#print axioms compose_identity
#print axioms compose_assoc
#print axioms maps_fixed_point
#print axioms maps_iterate
#print axioms composite_maps_fixed_point

end Wormhole

end D5.S3.Observer.Bridges.WormholeCategory
