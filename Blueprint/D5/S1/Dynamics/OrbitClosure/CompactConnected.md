# Compact Connected Orbit Closures

## Abstract

Continuous real-orbit closures in compact metric spaces are compact and connected.

**Theorem 1.1 (A continuous real-orbit closure is compact and connected).**

$$\operatorname{Compact}(\operatorname{cl}(\operatorname{range}(t\mapsto\phi(t,\xi_{0})))) \land \operatorname{Connected}(\operatorname{cl}(\operatorname{range}(t\mapsto\phi(t,\xi_{0}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/OrbitClosure/CompactConnected.orbit_closure_is_compact_and_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the orbit of xi0 be the range of t mapped to flow(t, xi0), where flow is continuous on the product of the real line and W. Its closure is closed in compact W, hence compact.

The real line is connected. Its continuous orbit image is therefore connected, and connectedness is preserved by taking closure.

Pinned Mathlib provides isConnected_range, IsConnected.closure, and IsClosed.isCompact. No single searched declaration combines both conclusions, so the proof is their thinnest direct composition.

## References

- Truth anchor: `D5/S1/Dynamics/OrbitClosure/CompactConnected.orbit_closure_is_compact_and_connected`
