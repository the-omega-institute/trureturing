# Wormhole Category

## Abstract

Typed semiconjugate bridges compose and transport fixed behavior.

**Theorem 1.1 (Identity Compose).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, bridge: Wormhole source target,\\{}(compose (identity target) bridge = bridge).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeCategory.identity_compose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Left identity for wormhole composition.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Compose Identity).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, bridge: Wormhole source target,\\{}(compose bridge (identity source) = bridge).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeCategory.compose_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right identity for wormhole composition.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Compose Assoc).**

$$\forall source: DynamicalWorld, middle: DynamicalWorld, target: DynamicalWorld, fourth: DynamicalWorld, third: Wormhole target fourth, second: Wormhole middle target, first: Wormhole source middle,\\{}(compose third (compose second first) = compose (compose third second) first).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeCategory.compose_assoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Associativity of wormhole composition.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Maps Fixed Point).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, bridge: Wormhole source target, state: source.State,\\{}(Function.IsFixedPt source.step state) \Rightarrow\\{}(Function.IsFixedPt target.step (bridge.map state)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeCategory.maps_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A wormhole transports every fixed source state to a fixed target state.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Maps Iterate).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, bridge: Wormhole source target, iteration: \mathbb{N}, state: source.State,\\{}(bridge.map ((source.step^{[iteration]}) state) = (target.step^{[iteration]}) (bridge.map state)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeCategory.maps_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A wormhole transports every finite iterate of the source dynamics.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.6 (Composite Maps Fixed Point).**

$$\forall source: DynamicalWorld, middle: DynamicalWorld, target: DynamicalWorld, second: Wormhole middle target, first: Wormhole source middle, state: source.State,\\{}(Function.IsFixedPt source.step state) \Rightarrow\\{}(Function.IsFixedPt target.step ((compose second first).map state)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeCategory.composite_maps_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Composite wormholes transport fixed points across multiple worlds.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/Bridges/WormholeCategory.compose_assoc`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeCategory.compose_identity`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeCategory.composite_maps_fixed_point`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeCategory.identity_compose`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeCategory.maps_fixed_point`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeCategory.maps_iterate`
- Dependency: [D5/S3/Observer/Bridges/FixedPointSemiconjugacy](FixedPointSemiconjugacy.md)
