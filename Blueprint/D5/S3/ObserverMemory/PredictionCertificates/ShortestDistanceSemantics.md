# Shortest-Distance Semantics

## Abstract

First-mismatch distance exactly measures future separation and stable depth.

**Theorem 1.1 (First separation determines distance and stable depth).**

$$\begin{gathered}\forall Y, O,\\{}\operatorname{FiniteNonempty}(Y), \tau: Y \to Y, q: Y \to O,\\{}\forall y, y'\in Y, (d_{q}(y, y') < \infty) \Leftrightarrow (\exists k\in \mathbb{N}, q(\tau^{k}(y)) \neq q(\tau^{k}(y'))),\\{}\forall k\in \mathbb{N}, (d_{q}(y, y') = k) \Leftrightarrow (q(\tau^{k}(y)) \neq q(\tau^{k}(y')) \land \forall j < k, q(\tau^{j}(y)) = q(\tau^{j}(y'))),\\{}(d_{q}(y, y') = \infty) \Leftrightarrow (\forall k\in \mathbb{N}, q(\tau^{k}(y)) = q(\tau^{k}(y'))),\\{}((\exists y, y'\in Y, d_{q}(y, y') < \infty) \Rightarrow m_{*} = \max\{d_{q}(y, y') \mid y, y'\in Y, d_{q}(y, y') < \infty\}) \land\\{}((\forall y, y'\in Y, d_{q}(y, y') = \infty) \Rightarrow m_{*} = 0).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/ShortestDistanceSemantics.shortest_distance_exact_semantics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be a finite nonempty state carrier, tau its deterministic update, and q a readout. The imported canonical distance is the least future readout-mismatch time, with none representing infinity.

The public statement gives both the existence criterion and the exact least-time characterization. Infinite distance is stated directly as equality at every future readout time.

The canonical least observation-stability depth equals the largest finite pair distance. The finite supremum uses zero for infinite entries, so the separate no-distinguishable-pair clause yields the source convention that the depth is zero.

The proof applies the existing infinity criterion and finite-history stability theorem. Pinned Mathlib's least-witness and finite-supremum lemmas bridge the two canonical depth objects; no distance, relation, or stability primitive is redeclared.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/ShortestDistanceSemantics.shortest_distance_exact_semantics`
- Dependency: [D5/S3/Observer/Separation/FiniteHistoryStability](../../Observer/Separation/FiniteHistoryStability.md)
- Dependency: [D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateMinimality](LocalCertificateMinimality.md)
