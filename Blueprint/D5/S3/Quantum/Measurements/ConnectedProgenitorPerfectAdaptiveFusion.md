# Connected progenitor graphs give perfect adaptive fusion

## Abstract

Goodenough, Landahl, Lee, Russo and Thompson (arXiv:2609.02559) conjecture that every [[n, 1, d]] graph code with a connected progenitor graph has a perfect adaptive fusion strategy: the physical fusions can be attempted in an order, with failure axes chosen from the earlier outcomes, so that a single successful physical fusion always gives a successful logical fusion. With the paper's failure criterion (Proposition 3.1), this holds: attempt the vertices farthest from the encoding vertex first with failure axis Z, and after the first success use axis X on the internal vertices of a shortest path from the encoding vertex to the successful vertex.

**Definition 1.1 (Pauli letters up to phase).**

$$\operatorname{Pauli} = \operatorname{Bool} \times \operatorname{Bool}$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.Pauli` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

A single-qubit Pauli operator up to phase is recorded by its two bits (x, z): I = (false, false), X = (true, false), Z = (false, true), Y = (true, true).

**Definition 1.2 (The identity letter).**

$$\operatorname{pauliI} = (\operatorname{false}, \operatorname{false})$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.pauliI` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

The identity letter has both bits false.

**Definition 1.3 (Products of canonical generators).**

$$\forall V \in \operatorname{Type},\; \operatorname{DecidableEq}\left(V\right) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow (\forall U \in \operatorname{Finset}\left(V\right),\; \forall w \in V,\; \operatorname{genProduct}\left(G, U, w\right) = (\operatorname{decide}\left(w \in U\right), \operatorname{decide}\left(\operatorname{Odd}\left(\operatorname{card}\left(\operatorname{filter}\left(\operatorname{Adj}\left(G, w\right), U\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.genProduct` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

For a finite simple graph G on a type V with decidable equality and decidable adjacency, the product over a set U of the canonical generators X_u times the product of Z_w over the neighbours w of u has, up to phase, the letter at w with x-bit 'w is in U' and z-bit 'w has an odd number of neighbours in U'. These products are, up to phase, all stabilizers of the graph state.

**Definition 1.4 (Non-trivial logical operators).**

$$\forall V \in \operatorname{Type},\; \operatorname{DecidableEq}\left(V\right) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow (\forall e \in V,\; \forall P \in V \to \operatorname{Pauli},\; \operatorname{IsNontrivialLogical}\left(G, e, P\right) \Leftrightarrow (\exists U \in \operatorname{Finset}\left(V\right),\; \left(\forall w \in V,\; w \ne e \Rightarrow (P\left(w\right) = \operatorname{genProduct}\left(G, U, w\right))\right) \land \operatorname{genProduct}\left(G, U, e\right) \ne \operatorname{pauliI})))$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.IsNontrivialLogical` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

For the progenitor graph G with encoding vertex e, a Pauli string P on the physical vertices is a non-trivial logical operator when it is the restriction to the vertices other than e of a graph-state stabilizer that is not the identity at e.

**Definition 1.5 (Adaptive fusion strategies).**

$$\forall V \in \operatorname{Type},\; \forall e \in V,\; \forall S \in \operatorname{AdaptiveStrategy}\left(e\right),\; \left(\operatorname{rank}\left(S\right) \in V \to \mathbb{Z} \land \operatorname{axis}\left(S\right) \in V \to V \to \operatorname{Bool} \to \operatorname{Pauli}\right) \land \left(\left(\forall a \in V,\; \forall b \in V,\; a \ne e \Rightarrow (b \ne e \Rightarrow (\operatorname{rank}\left(S, a\right) = \operatorname{rank}\left(S, b\right) \Rightarrow (a = b)))\right) \land \left(\left(\forall w \in V,\; \forall o \in V \to \operatorname{Bool},\; \operatorname{axis}\left(S, w, o\right) \ne \operatorname{pauliI}\right) \land \left(\forall w \in V,\; \forall o \in V \to \operatorname{Bool},\; \forall r \in V \to \operatorname{Bool},\; \left(\forall u \in V,\; u \ne e \Rightarrow (\operatorname{rank}\left(S, u\right) < \operatorname{rank}\left(S, w\right) \Rightarrow (o\left(u\right) = r\left(u\right)))\right) \Rightarrow (\operatorname{axis}\left(S, w, o\right) = \operatorname{axis}\left(S, w, r\right))\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.AdaptiveStrategy` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

An adaptive strategy attempts the physical vertices in increasing rank, the rank being injective on the vertices other than e, and gives each vertex a non-identity failure axis that depends only on the outcomes o (true for a successful fusion) of the physical vertices of smaller rank.

**Definition 1.6 (Logical failure).**

$$\forall V \in \operatorname{Type},\; \operatorname{DecidableEq}\left(V\right) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow (\forall e \in V,\; \forall S \in \operatorname{AdaptiveStrategy}\left(e\right),\; \forall o \in V \to \operatorname{Bool},\; \operatorname{LogicalFailure}\left(G, e, S, o\right) \Leftrightarrow (\exists P \in V \to \operatorname{Pauli},\; \operatorname{IsNontrivialLogical}\left(G, e, P\right) \land \left(\forall w \in V,\; w \ne e \Rightarrow (\left(o\left(w\right) = \operatorname{false} \Rightarrow (P\left(w\right) = \operatorname{pauliI} \lor P\left(w\right) = \operatorname{axis}\left(S, w, o\right))\right) \land \left(o\left(w\right) = \operatorname{true} \Rightarrow (P\left(w\right) = \operatorname{pauliI})\right))\right))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.LogicalFailure` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

Proposition 3.1 of the paper: the outcome o leads to a logical failure when some non-trivial logical operator is, at every failed vertex, the identity or the realized failure axis, and is the identity at every vertex whose fusion succeeded.

**Definition 1.7 (Perfect adaptive strategies).**

$$\forall V \in \operatorname{Type},\; \operatorname{DecidableEq}\left(V\right) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow (\forall e \in V,\; \operatorname{HasPerfectAdaptiveStrategy}\left(G, e\right) \Leftrightarrow (\exists S \in \operatorname{AdaptiveStrategy}\left(e\right),\; \forall o \in V \to \operatorname{Bool},\; \left(\exists w \in V,\; w \ne e \land o\left(w\right) = \operatorname{true}\right) \Rightarrow (\neg \operatorname{LogicalFailure}\left(G, e, S, o\right)))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.HasPerfectAdaptiveStrategy` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

Some adaptive strategy avoids a logical failure for every outcome with at least one successful physical fusion.

**Definition 1.8 (The conjecture).**

$$claim \Leftrightarrow (\forall V \in \operatorname{Type},\; \operatorname{Fintype}\left(V\right) \Rightarrow (\operatorname{DecidableEq}\left(V\right) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right) \Rightarrow (\forall e \in V,\; \operatorname{Connected}\left(G\right) \Rightarrow (\left(\exists w \in V,\; \operatorname{Adj}\left(G, e, w\right)\right) \Rightarrow (\operatorname{HasPerfectAdaptiveStrategy}\left(G, e\right)))))))$$

*Formalization.* `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.claim` (`✓ std3`).

*Citation.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

Every graph code whose progenitor graph is a connected finite simple graph, with the encoding vertex incident to an edge, has a perfect adaptive strategy.

**Theorem 1.9 (Proof of the conjecture).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.result` (`✓ std3`). ∎

*Resolves.* `Problems/goodenough-landahl-2026-connected-progenitor-adaptive-fusion` (proved) by `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"goodenough-landahl-2026-connected-progenitor-adaptive-fusion","declaration_gid":"D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Goodenough, Andrew Landahl, Joon Lee, Antonio Russo and Kevin Thompson (2026). *Optimal Fusion Strategies for Quantum Computation*. URL: <https://arxiv.org/abs/2609.02559>.

*Commentary.*

Attempt the physical vertices in order of decreasing graph distance from e, with failure axis Z until the first success. If the first success is at v, at distance l from e, fix a shortest path e = p(l), ..., p(1), p(0) = v that steps from each vertex to a neighbour one closer to e; its internal vertices are closer to e than v, so they have not been attempted, and from then on the axis is X on them and Z elsewhere. This choice uses only earlier outcomes. Adjacent vertices have distances differing by at most 1, so p(i) and p(j) are adjacent only when |i - j| = 1. Suppose a stabilizer product over U gives a logical failure. Off the path the vertex failed in Z or succeeded, so its x-bit is 0 and it is not in U; hence U lies on the path. At an internal path vertex the letter is I or X, and at v it is I, so each of these has an even number of neighbours in U. Since U lies on the path, the neighbours of p(i) in U are among p(i - 1) and p(i + 1). At v this gives p(1) not in U, and at p(i) for 1 <= i < l it gives that p(i + 1) is in U exactly when p(i - 1) is. Starting from p(0) and p(1) not in U, induction gives that no path vertex is in U. So U is empty and the stabilizer is the identity at e, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.AdaptiveStrategy`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.HasPerfectAdaptiveStrategy`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.IsNontrivialLogical`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.LogicalFailure`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.Pauli`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.claim`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.genProduct`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.pauliI`
- Truth anchor: `D5/S3/Quantum/Measurements/ConnectedProgenitorPerfectAdaptiveFusion.result`
