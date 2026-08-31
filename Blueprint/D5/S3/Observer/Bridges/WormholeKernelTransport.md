# Wormhole Kernel Transport

## Abstract

Wormhole composition records exact observer-kernel loss.

**Theorem 1.1 (Kernel Forward Invariant).**

$$\forall source: DynamicalWorld, target: DynamicalWorld, bridge: Wormhole source target, first: source.State, second: source.State,\\{}(Setoid.ker bridge.map first second) \Rightarrow\\{}(Setoid.ker bridge.map (source.step first) (source.step second)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeKernelTransport.kernel_forward_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The observation kernel of a wormhole is forward-invariant under the source dynamics.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.2 (Kernel le Composite).**

$$\forall source: DynamicalWorld, middle: DynamicalWorld, target: DynamicalWorld, first: Wormhole source middle, second: Wormhole middle target,\\{}(Setoid.ker first.map \leq Setoid.ker (compose second first).map).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeKernelTransport.kernel_le_composite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Postcomposing a wormhole can only enlarge its source observer kernel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.3 (Kernel eq Composite Of Outer Injective).**

$$\forall source: DynamicalWorld, middle: DynamicalWorld, target: DynamicalWorld, first: Wormhole source middle, second: Wormhole middle target,\\{}(Function.Injective second.map) \Rightarrow\\{}(Setoid.ker (compose second first).map = Setoid.ker first.map).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeKernelTransport.kernel_eq_composite_of_outer_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An injective outer wormhole preserves the source observer kernel exactly.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.4 (Strict Kernel Growth Of Outer Collision).**

$$\forall source: DynamicalWorld, middle: DynamicalWorld, target: DynamicalWorld, first: Wormhole source middle, second: Wormhole middle target, left: source.State, right: source.State,\\{}(first.map left \neq first.map right) \land (second.map (first.map left) = second.map (first.map right)) \Rightarrow\\{}(Setoid.ker first.map < Setoid.ker (compose second first).map).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeKernelTransport.strict_kernel_growth_of_outer_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A pair visible after the first bridge but collapsed by the second bridge witnesses strict growth of the composite kernel.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

**Theorem 1.5 (Strict Growth Refutes Outer Injectivity).**

$$\forall source: DynamicalWorld, middle: DynamicalWorld, target: DynamicalWorld, first: Wormhole source middle, second: Wormhole middle target,\\{}(Setoid.ker first.map < Setoid.ker (compose second first).map) \Rightarrow\\{}(\neg Function.Injective second.map).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Bridges/WormholeKernelTransport.strict_growth_refutes_outer_injectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict information loss through a composite refutes injectivity of the outer bridge.

The declaration keeps its parameters and hypotheses explicit; the result makes no converse or broader existence claim beyond that scope.

## References

- Truth anchor: `D5/S3/Observer/Bridges/WormholeKernelTransport.kernel_eq_composite_of_outer_injective`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeKernelTransport.kernel_forward_invariant`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeKernelTransport.kernel_le_composite`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeKernelTransport.strict_growth_refutes_outer_injectivity`
- Truth anchor: `D5/S3/Observer/Bridges/WormholeKernelTransport.strict_kernel_growth_of_outer_collision`
- Dependency: [D5/S3/Observer/Bridges/WormholeCategory](WormholeCategory.md)
