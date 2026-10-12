# Minimal bipartite Erdős–Gyárfás counterexamples have no bridge

## Abstract

A minimal bipartite graph of minimum degree at least three without a power-of-two cycle is connected and has no bridge.

**Definition 1.1 (Power-of-two cycles).**

$$\forall V \in \mathrm{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{HasPowTwoCycle}\left(G\right) \Leftrightarrow \left(\exists v \in V,\; \exists c \in \operatorname{Walk}\left(G, v, v\right),\; \operatorname{IsCycle}\left(c\right) \land \left(\exists k \in \mathrm{Nat},\; 2 \le k \land \operatorname{length}\left(c\right) = 2^{k}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.HasPowTwoCycle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The allowed exponents are the natural numbers at least two, so the excluded cycle lengths are four, eight, sixteen, and so on.

**Definition 1.2 (Bipartite counterexamples).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsBipCounterexample}\left(G\right) \Leftrightarrow \left(\operatorname{Nonempty}\left(V\right) \land \left(\operatorname{Colorable}\left(G, 2\right) \land \left(\left(\forall v \in V,\; 3 \le \operatorname{degree}\left(G, v\right)\right) \land \left(\neg \operatorname{HasPowTwoCycle}\left(G\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.IsBipCounterexample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex type is nonempty, the graph admits a proper two-colouring, every degree is at least three, and no cycle has an allowed length.

**Definition 1.3 (Lexicographic minimality).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsMinimalBipCounterexample}\left(G\right) \Leftrightarrow \left(\operatorname{IsBipCounterexample}\left(G\right) \land \left(\forall W \in \mathrm{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall H \in \operatorname{SimpleGraph}\left(W\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(H\right)\right)] \operatorname{IsBipCounterexample}\left(H\right) \Rightarrow \left(\operatorname{card}\left(V\right) < \operatorname{card}\left(W\right) \lor \left(\operatorname{card}\left(V\right) = \operatorname{card}\left(W\right) \land \operatorname{card}\left(\operatorname{edgeFinset}\left(G\right)\right) \le \operatorname{card}\left(\operatorname{edgeFinset}\left(H\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.IsMinimalBipCounterexample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compare with every counterexample on every finite vertex type. The vertex count is minimal, and among equal vertex counts the edge count is minimal.

**Definition 1.4 (Two-edge-connectivity assertion).**

$$claim \Leftrightarrow \left(\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsMinimalBipCounterexample}\left(G\right) \Rightarrow \left(\operatorname{Connected}\left(G\right) \land \left(\forall e \in \operatorname{Sym2}\left(V\right),\; e \in \operatorname{edgeSet}\left(G\right) \Rightarrow \operatorname{Connected}\left(\operatorname{deleteEdges}\left(G, \{e\}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every minimal bipartite counterexample is connected, and deleting any one of its edges leaves a connected graph.

**Theorem 1.5 (Minimal counterexamples are connected).**

$$\forall V \in \mathrm{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsMinimalBipCounterexample}\left(G\right) \Rightarrow \operatorname{Connected}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.minimal_connected` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An induced connected component retains every vertex degree. Its inclusion preserves the colouring and all cycle lengths. A proper component would therefore be a counterexample with fewer vertices.

**Theorem 1.6 (Minimal counterexamples have no bridge).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result` (`✓ std3`). ∎

*Resolves.* `Problems/ducoffe-dumitru-2026-bipartite-minimal-two-edge-connected` (proved) by `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"ducoffe-dumitru-2026-bipartite-minimal-two-edge-connected","declaration_gid":"D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Contract a bridge and exchange the two colours on one component. Every retained degree is at least three, while the merged vertex has degree at least four. A cycle stays on one side of the merged vertex and lifts to a cycle of the original graph of equal length. The contracted graph has fewer vertices, contradicting minimality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.HasPowTwoCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.IsBipCounterexample`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.IsMinimalBipCounterexample`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.minimal_connected`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasBipartiteBridgeless.result`
- Dependency: [D5/S3/Combinatorics/Graph/ErdosGyarfasBridgeContraction](ErdosGyarfasBridgeContraction.md)
