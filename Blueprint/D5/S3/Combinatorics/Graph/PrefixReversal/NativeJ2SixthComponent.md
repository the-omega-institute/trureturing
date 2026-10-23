# The Sixth Actual J2 Path Component

## Abstract

The two remaining independently specified J2 ports are joined by a sixth actual complete path component.

**Theorem 1.1 (The Actual Component from L1 to Bar L0).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\exists w \in \mathrm{Walk}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{port}\left(m, \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{True}\right)\right), \mathrm{port}\left(m, \mathrm{Tuple3}\left(0, \mathrm{True}, \mathrm{True}\right)\right)\right),\; \mathrm{IsPath}\left(w\right) \land \left(\left(\forall x \in \mathrm{Configuration}\left(m\right),\; \mathrm{Member}\left(x, \mathrm{Support}\left(w\right)\right) \Leftrightarrow \mathrm{Reachable}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{port}\left(m, \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{True}\right)\right), x\right)\right) \land \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \forall y \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Adj}\left(\mathrm{survivingGraph}\left(m\right), x, y\right) \land \mathrm{Reachable}\left(\mathrm{survivingGraph}\left(m\right), \mathrm{port}\left(m, \mathrm{Tuple3}\left(1, \mathrm{False}, \mathrm{True}\right)\right), x\right)\right) \Leftrightarrow \mathrm{Member}\left(\mathrm{Sym2Pair}\left(x, y\right), \mathrm{Edges}\left(w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SixthComponent.native_j2_sixth_full_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, the theorem constructs an actual simple path in survivingGraph(m) from port(m,(1,false,true)) to port(m,(0,true,true)). Its support consists exactly of all vertices reachable from the first port, and it contains every actual surviving edge incident to that component.

Apply the endpoint-aware six-cut slicing theorem to the same actual F2 Hamilton cycle containing the six independently specified marked edges. Map and transfer the resulting subtype walks into the actual surviving graph. Their supports partition the full F2 domain and their edges are exactly the surviving inventory. Disjointness and edge saturation therefore make each piece a whole component. Every port is a graph leaf, so it can occur only at a path endpoint. The five constructed literal word components exclude ten of the twelve ports from the component of L1. The actual surviving a edge at L1 rules out a nil piece. Its other endpoint must consequently be bar L0, and reversing the actual slice when necessary earns the stated orientation.

Higher actual recursive expansion and Hamilton cycles for all sizes remain separate obligations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SixthComponent.native_j2_sixth_full_component`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingEdges](NativeJ2SurvivingEdges.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/EdgeSlicingCutEndpoints](../Walks/EdgeSlicingCutEndpoints.md)
