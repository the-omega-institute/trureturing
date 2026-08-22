# Quotient-Fiber Entropy Decomposition

## Abstract

A finite source law splits into quotient entropy and weighted normalized-fiber entropy.

**Theorem 1.1 (Finite source entropy splits over quotient fibers).**

$$\begin{gathered}\forall X, B, \operatorname{Finite}\left(X\right) \land \operatorname{Finite}\left(B\right),\\p: X \to \mathbb{R}, q: X \to B,\\\operatorname{nonnegative}\left(p\right) \land \sum_{x}p(x) = 1 \Rightarrow\\\operatorname{H}\left(p\right) = \operatorname{H}\left(\operatorname{push}\left(q, p\right)\right) + \sum_{b\in B}\operatorname{push}\left(q, p\right)(b)\operatorname{H}\left(\operatorname{conditional}\left(\operatorname{push}\left(x \mapsto \operatorname{pair}\left(q(x), x\right), p\right), b\right)\right) \land\\\operatorname{H}\left(p\right) = \operatorname{H}\left(\operatorname{push}\left(q, p\right)\right) + \operatorname{Hcond}\left(\operatorname{push}\left(x \mapsto \operatorname{pair}\left(q(x), x\right), p\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Fusion/QuotientFiberDecomposition.quotient_fiber_entropy_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X and B be finite, let p be a nonnegative normalized mass on X, and let q map X to B. The quotient law is the deterministic pushforward of p along q.

The graph map sends x to (q(x),x). Conditioning its pushforward at b constructs the normalized source law on the fiber over b, with zero contribution when the quotient mass at b vanishes.

The first equality exposes the quotient-mass-weighted fiber sum. The second exposes the same decomposition through the canonical conditional-entropy aggregate. Injectivity of the graph map identifies graph-law entropy with source entropy, after which the finite Shannon chain rule supplies both conclusions.

## References

- Truth anchor: `D5/S3/Entropy/Fusion/QuotientFiberDecomposition.quotient_fiber_entropy_decomposition`
- Dependency: [D5/S3/Entropy/Forgetting/DeterministicEntropyEquality](../Forgetting/DeterministicEntropyEquality.md)
