# The Correlation Blind Spot of Local Marginals

## Abstract

Complete local marginals leave every cross-factor correlation direction unread.

**Theorem 1.1 (Complete local data omit the full correlation sector).**

$$\begin{gathered}\forall m, n, m \geq 1 \land n \geq 1 \land {m} \times {n} > 1 \Rightarrow \\{}\operatorname{Sup}\left(\operatorname{localASector}\left(m, n\right), \operatorname{localBSector}\left(m, n\right), \operatorname{correlationSector}\left(m, n\right)\right) = \operatorname{bipartiteTraceZero}\left(m, n\right) \land\\{}\operatorname{finrankR}\left(\operatorname{Sup}\left(\operatorname{localASector}\left(m, n\right), \operatorname{localBSector}\left(m, n\right)\right)\right) = {{m}^{{2}} - 1} + {{n}^{{2}} - 1} \land\\{}\operatorname{finrankR}\left(\operatorname{correlationSector}\left(m, n\right)\right) = {{m}^{{2}} - 1} \times {{n}^{{2}} - 1} \land\\{}\frac{\operatorname{finrankR}\left(\operatorname{correlationSector}\left(m, n\right)\right)}{\operatorname{finrankR}\left(\operatorname{bipartiteTraceZero}\left(m, n\right)\right)} = \frac{{{m}^{{2}} - 1} \times {{n}^{{2}} - 1}}{{{m}^{{2}}} {{n}^{{2}}} - 1} \land\\{}\operatorname{Orthogonal}\left(\operatorname{Sup}\left(\operatorname{localASector}\left(m, n\right), \operatorname{localBSector}\left(m, n\right)\right), \operatorname{correlationSector}\left(m, n\right)\right) \land\\{}\operatorname{PosSemidef}\left(\operatorname{bellDensity}\right) \land \operatorname{Tr}\left(\operatorname{bellDensity}\right) = 1 \land \operatorname{rank}\left(\operatorname{bellDensity}\right) = 1 \land\\{}\operatorname{PosSemidef}\left(\operatorname{classicalCorrelatedDensity}\right) \land \operatorname{Tr}\left(\operatorname{classicalCorrelatedDensity}\right) = 1 \land {\operatorname{classicalCorrelatedDensity}}^{{2}} \neq \operatorname{classicalCorrelatedDensity} \land\\{}\operatorname{traceEnvironment}\left(\operatorname{bellDensity}\right) = \operatorname{traceEnvironment}\left(\operatorname{classicalCorrelatedDensity}\right) \land\\{}\operatorname{traceFirstFactor}\left(\operatorname{bellDensity}\right) = \operatorname{traceFirstFactor}\left(\operatorname{classicalCorrelatedDensity}\right) \land\\{}\operatorname{bellDensity} \neq \operatorname{classicalCorrelatedDensity}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.local_marginal_correlation_blind_spot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two positive finite factor dimensions with nontrivial product, the locally visible directions are the join of the two canonical local Hermitian sectors. Their real dimension is the sum of the two local traceless dimensions.

The orthogonal unread sector is the canonical correlation sector. It has the product dimension, and its dimension divided by the full traceless dimension is the displayed correlation proportion.

The final clauses give an explicit witness. The canonical Bell density is a positive trace-one rank-one state, while the diagonal equal mixture of the 00 and 11 basis states is a positive trace-one non-idempotent state.

Both canonical partial traces agree for these two densities, but the global matrices differ. Thus even complete knowledge of both local marginals does not determine cross-factor correlations.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.local_marginal_correlation_blind_spot`
- Dependency: [D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal](BellPureStateMixedMarginal.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](BipartiteSectorDecomposition.md)
