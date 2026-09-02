# Single-Prime Visible Space

## Abstract

Single-prime Hermitian effects see exactly the scalar and singleton sectors.

**Theorem 1.1 (Single-prime readout leaves exactly the cross-prime sectors invisible).**

$$\begin{gathered}\forall \iota: \operatorname{Type}(), \operatorname{Fintype}(\iota), \operatorname{DecidableEq}(\iota),\\{}d: \iota \to \operatorname{Nat}(),\\{}\operatorname{IsInternal}(S \mapsto \operatorname{primeSector}(d, S)) \land\\{}(\forall S: \operatorname{Finset}(\iota), \operatorname{finrankR}(\operatorname{primeSector}(d, S)) = \prod_{j \in S} {d\left(j\right)^{2} - 1}) \Rightarrow\\{}\operatorname{singlePrimeVisibleSpace}(d) = \operatorname{Sup}(\operatorname{primeSector}(d, \emptyset), \operatorname{iSup}(i, i \mapsto \operatorname{primeSector}(d, \{i\}))) \land\\{}\operatorname{finrankR}(\operatorname{singlePrimeVisibleSpace}(d)) = 1 + \sum_{i \in \iota} {d\left(i\right)^{2} - 1} \land\\{}\operatorname{finrankR}(\operatorname{invisibleTraceZeroResidual}(d)) = {\prod_{i \in \iota} d\left(i\right)}^{2} - 1 - \sum_{i \in \iota} {d\left(i\right)^{2} - 1} \land\\{}\operatorname{invisibleTraceZeroResidual}(d) = \operatorname{iSup}(\{S: \operatorname{Finset}(\iota) \mid 2 \leq \operatorname{card}(S)\}, S \mapsto \operatorname{primeSector}(d, S)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SinglePrimeVisibleSpace.single_prime_visible_space` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite family of local Hilbert dimensions, primeSector is the repository's canonical tensor sector: factors in S are traceless Hermitian and factors outside S are scalar Hermitian.

The standing internal-decomposition and sector-rank hypotheses are the formal counterparts of the orthogonal sector expansion immediately preceding theorem 119.1 in the source.

The four conclusion clauses identify the visible space, compute its real dimension, compute the invisible trace-zero residual dimension, and identify that residual with exactly the sectors supported on at least two factors.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SinglePrimeVisibleSpace.single_prime_visible_space`
- Dependency: [D5/S3/Quantum/Dynamics/ProductDynamicsLocalSupport](../Dynamics/ProductDynamicsLocalSupport.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](BipartiteSectorDecomposition.md)
