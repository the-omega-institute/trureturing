# Least Invariant Observable Algebra

## Abstract

Bounded readout pullbacks reach the least invariant observable algebra at the least stable depth.

**Theorem 1.1 (Finite pullbacks reach the least invariant algebra).**

$$\begin{gathered}\forall Y, O: \operatorname{Type}, [\operatorname{Fintype}(Y)], [\operatorname{Nonempty}(Y)],\\{}\tau: Y \to Y, q: Y \to O, \operatorname{Surjective}(q),\\{}m_{*} := \operatorname{predictionStabilityDepth}(\tau, q),\\{}(\forall i, j\in \mathbb{N}, i \le j \Rightarrow \operatorname{finiteKoopmanClosure}(\tau, q, i) \le \operatorname{finiteKoopmanClosure}(\tau, q, j)) \land\\{}\operatorname{finiteKoopmanClosure}(\tau, q, m_{*}) = \operatorname{finiteKoopmanClosure}(\tau, q, m_{*} + 1) \land\\{}\operatorname{PullbackInvariant}(\tau, \operatorname{finiteKoopmanClosure}(\tau, q, m_{*})) \land\\{}\operatorname{finiteKoopmanClosure}(\tau, q, m_{*}) = \operatorname{sInf}(\operatorname{invariantObservableExtensions}(\tau, q)) \land\\{}(\forall f\in \operatorname{finiteKoopmanClosure}(\tau, q, m_{*}), y\in Y, \operatorname{stableObservableAlgebraEquiv}(\tau, q)(f)(\operatorname{completionProjection}(\tau, q, y)) = f(y)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra.least_invariant_observable_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The current observable algebra is the range of complex-function pullback along the surjective readout. The depth algebra is constructed by adjoining its pullbacks through update times at most that depth.

The first two public clauses state monotonicity of the entire finite chain and equality of consecutive stages at the source's least prediction-stable depth. The third states closure under one further pullback.

The fourth clause identifies the stable stage with the infimum of every unital star subalgebra containing the current readout algebra and closed under pullback. The final clause exposes the named canonical equivalence to functions on complete prediction states and gives its value on every projected representative.

The proof applies the frozen full-closure theorem, permanent partition stability, and stabilized quotient equivalence directly.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra.least_invariant_observable_algebra`
- Dependency: [D5/S3/ObserverMemory/Refinement/GradedPredictionShift](../../ObserverMemory/Refinement/GradedPredictionShift.md)
- Dependency: [D5/S3/QuantumStates/ObservableAlgebraClosureDuality](../../QuantumStates/ObservableAlgebraClosureDuality.md)
