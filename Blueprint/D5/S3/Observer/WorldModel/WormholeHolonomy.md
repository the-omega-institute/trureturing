# Wormhole Holonomy

## Abstract

Round trips through observer wormholes define holonomy, with inverse bridges giving the trivial loop.

**Theorem 1.1 (Round Trip Maps Fixed Point).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, forward: Wormhole source target, backward: Wormhole target source, state: source.State,\\{}(Function.IsFixedPt source.step state) \Rightarrow\\{}(Function.IsFixedPt source.step ((roundTrip forward backward).map state)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/WormholeHolonomy.round_trip_maps_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Round trips preserve every fixed source state as a fixed state of the round-trip dynamics.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Round Trip eq Identity Of Left Inverse).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, forward: Wormhole source target, backward: Wormhole target source,\\{}(Function.LeftInverse backward.map forward.map) \Rightarrow\\{}(roundTrip forward backward = identity source).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/WormholeHolonomy.round_trip_eq_identity_of_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A genuine left inverse makes the round trip equal to the identity wormhole.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (No Holonomy Of Left Inverse).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, forward: Wormhole source target, backward: Wormhole target source, state: source.State,\\{}(Function.LeftInverse backward.map forward.map) \Rightarrow\\{}(\neg HasHolonomyAt forward backward state).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/WormholeHolonomy.no_holonomy_of_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A left inverse rules out holonomy at every source state.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Holonomy Refutes Left Inverse).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, forward: Wormhole source target, backward: Wormhole target source, state: source.State,\\{}(HasHolonomyAt forward backward state) \Rightarrow\\{}(\neg Function.LeftInverse backward.map forward.map).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/WorldModel/WormholeHolonomy.holonomy_refutes_left_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any holonomy witness refutes the claim that the return bridge is a left inverse.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/WorldModel/WormholeHolonomy.holonomy_refutes_left_inverse`
- Truth anchor: `D5/S3/Observer/WorldModel/WormholeHolonomy.no_holonomy_of_left_inverse`
- Truth anchor: `D5/S3/Observer/WorldModel/WormholeHolonomy.round_trip_eq_identity_of_left_inverse`
- Truth anchor: `D5/S3/Observer/WorldModel/WormholeHolonomy.round_trip_maps_fixed_point`
- Dependency: [D5/S3/Observer/Bridges/WormholeCategory](../Bridges/WormholeCategory.md)
