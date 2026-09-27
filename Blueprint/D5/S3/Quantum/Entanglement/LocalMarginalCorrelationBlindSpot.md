# The Correlation Blind Spot of Local Marginals

## Abstract

Complete local marginals leave every cross-factor correlation direction unread.

In the real Hermitian tensor model with factor dimensions $m, n$, write $L$ for the sum of the canonical traceless local sectors, $C$ for the sector traceless in both factors, and $H_{0}$ for the full traceless space. Sector dimensions and orthogonality are real.

Independently, $\rho$ is the canonical two-qubit Bell density for 00 and 11, and $\sigma$ their equal diagonal mixture. Here $\geq 0$ means positive semidefinite; partial-trace subscripts name the factor traced out.

**Theorem 1.1 (Complete local data omit the full correlation sector).**

$$
\begin{gathered}\forall m, n \in \mathbb{N},\\\ {}m \geq 1 \land n \geq 1 \land mn > 1 \Rightarrow\\\ {}L + C = H_{0} \land\\\ {}\mathrm{dim}(L) = (m^{2} - 1) + (n^{2} - 1) \land\\\ {}\mathrm{dim}(C) = (m^{2} - 1)(n^{2} - 1) \land\\\ {}\frac{\mathrm{dim}(C)}{\mathrm{dim}(H_{0})} = \frac{(m^{2} - 1)(n^{2} - 1)}{m^{2}n^{2} - 1} \land\\\ {}L \perp C \land\\\ {}\rho \geq 0 \land \mathrm{Tr}(\rho) = 1 \land \mathrm{rank}(\rho) = 1 \land\\\ {}\sigma \geq 0 \land \mathrm{Tr}(\sigma) = 1 \land \sigma^{2} \neq \sigma \land\\\ {}\mathrm{Tr}_{B}(\rho) = \mathrm{Tr}_{B}(\sigma) \land\\\ {}\mathrm{Tr}_{A}(\rho) = \mathrm{Tr}_{A}(\sigma) \land\\\ {}\rho \neq \sigma.\end{gathered}
$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.local_marginal_correlation_blind_spot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correlation sector is orthogonal to all local directions. The ratio gives its share of the traceless space.

The fixed witness has identical local marginals but different global matrices: complete local data need not determine cross-factor correlations.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/LocalMarginalCorrelationBlindSpot.local_marginal_correlation_blind_spot`
- Dependency: [D5/S3/Quantum/Entanglement/BellPureStateMixedMarginal](BellPureStateMixedMarginal.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](BipartiteSectorDecomposition.md)
