# Sequential Word Observation Residual

## Abstract

Instrument word expectations agree exactly on the generated orthogonal residual.

**Theorem 1.1 (Bounded instrument words characterize the orthogonal residual).**

$$\forall d: Nat, A, S: \operatorname{Type}, J: A\to\operatorname{HermitianSpace}(d) \to\operatorname{HermitianSpace}(d), X: S\to\operatorname{HermitianSpace}(d), rho, sigma: S, n: Nat \Rightarrow\\{}(\forall w: \operatorname{List}(A), \operatorname{length}(w) \le n \Rightarrow (\operatorname{inner}(\mathbb{R}, X(rho), \operatorname{sequentialWordEffect}(J, w)) = \operatorname{inner}(\mathbb{R}, X(sigma), \operatorname{sequentialWordEffect}(J, w)))) \Leftrightarrow (X(rho) - X(sigma) \in (\operatorname{span}(\mathbb{R}, (\exists e: \operatorname{HermitianSpace}(d), \exists w: \operatorname{List}(A), \operatorname{length}(w) \le n \land e = \operatorname{sequentialWordEffect}(J, w))))^{\perp}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/SequentialWordObservationResidual.sequential_observation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real Hermitian operator carrier, each instrument dual map acts on the identity effect. The public word-effect construction folds those maps in source order, matching the Heisenberg composition of a finite instrument word.

Two represented states have equal expectations for every word of length at most n exactly when their difference is orthogonal to the real span of all generated word effects.

## References

- Truth anchor: `D5/S3/Quantum/Completion/SequentialWordObservationResidual.sequential_observation_iff`
- Dependency: [D5/S3/Quantum/Algebra/FutureWordOrthogonalResidual](../Algebra/FutureWordOrthogonalResidual.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
