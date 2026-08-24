# Infinite Invariant Observable Algebra

## Abstract

The supremum of the finite pullback chain is the least invariant observable algebra.

**Theorem 1.1 (The infinite pullback chain stabilizes canonically).**

$$\forall Y, O: \operatorname{Type}, [\operatorname{Fintype}(Y)], [\operatorname{Nonempty}(Y)],\\{}tau: Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}\operatorname{infiniteKoopmanClosure}(tau, q) = \operatorname{finiteKoopmanClosure}(tau, q, \operatorname{predictionStabilityDepth}(tau, q)) \land \operatorname{initialObservableAlgebra}(q) \le \operatorname{infiniteKoopmanClosure}(tau, q) \land \operatorname{PullbackInvariant}(tau, \operatorname{infiniteKoopmanClosure}(tau, q)) \land \operatorname{infiniteKoopmanClosure}(tau, q) = \operatorname{sInf}(\operatorname{invariantObservableExtensions}(tau, q)) \land \forall f\in \operatorname{finiteKoopmanClosure}(tau, q, \operatorname{predictionStabilityDepth}(tau, q)), y\in Y, \operatorname{stableObservableAlgebraEquiv}(tau, q)(f)(\operatorname{completionProjection}(tau, q, y)) = f(y).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/InfiniteInvariantObservableAlgebra.infinite_invariant_observable_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The infinite algebra is the supremum of the canonical finite pullback closures. Finite-system leastness places every finite stage below the least invariant extension, while the stable stage is itself one of the supremum members.

The public clauses expose stabilization, current-readout containment, pullback invariance, leastness, and the canonical stable-state evaluation rule.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/InfiniteInvariantObservableAlgebra.infinite_invariant_observable_algebra`
- Dependency: [D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra](LeastInvariantObservableAlgebra.md)
