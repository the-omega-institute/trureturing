# The full dual account

## Abstract

Two mutually unbiased measurements connect the full coherence tax to entropy freedom.

The dimension d is a positive natural number. Density states are positive semidefinite complex matrices with trace one. Z and X are complete rank-one projective contexts; their projectors form record measurements. MutuallyUnbiased means ReTr(Z_j X_k) = 1/d for every pair of outcomes. unreadState denotes the sum of P_j rho P_j over a context. The zero-Hamiltonian Gibbs state omega is I/d. All logarithms are natural. Freedom means relative entropy to omega; the tax of a measurement is relative entropy from its input to its actual output.

**Theorem 1.1 (A Z-fixed state pays its full freedom in X).**

$$\forall d \in PositiveNatural, Z \in \operatorname{RankOneContext}\left(d\right), X \in \operatorname{RankOneContext}\left(d\right), rho \in \operatorname{DensityState}\left(d\right), sigma \in \operatorname{DensityState}\left(d\right),\; \left(\operatorname{IsRecordMeasurement}\left(Z\right) \land \left(\operatorname{IsRecordMeasurement}\left(X\right) \land \left(\operatorname{MutuallyUnbiased}\left(Z, X\right) \land \left(\operatorname{unreadState}\left(Z, rho\right) = rho \land \operatorname{unreadState}\left(X, rho\right) = sigma\right)\right)\right)\right) \Rightarrow \left(sigma = \operatorname{gibbsState}\left(0\right) \land \left(\operatorname{quantumRelativeEntropy}\left(rho, sigma\right) = \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(0\right)\right) \land \left(\operatorname{quantumRelativeEntropy}\left(rho, sigma\right) = \operatorname{log}\left(d\right) - \operatorname{vonNeumannEntropy}\left(rho\right) \land \left(\operatorname{vonNeumannEntropy}\left(sigma\right) - \operatorname{vonNeumannEntropy}\left(rho\right) = \operatorname{quantumRelativeEntropy}\left(rho, sigma\right) \land \left(\operatorname{unreadState}\left(X, rho\right) = rho \Leftrightarrow rho = \operatorname{gibbsState}\left(0\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/DualAccountFull.dual_account_full` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mutual unbiasedness makes the composition of the two measurements completely depolarizing. Since Z already fixes rho, the actual X output sigma must be omega. The Gibbs entropy identity then makes the X tax equal to log(d) minus the input entropy, and to the entropy gained in that measurement. If X also fixes rho, rho itself is omega; the converse follows from the same output equality. The proof also covers dimension one, where trace normalization fixes the only entry.

**Theorem 1.2 (Every state lies on the entropy and freedom segment).**

$$\forall d \in PositiveNatural, rho \in \operatorname{DensityState}\left(d\right),\; 0 \le \operatorname{vonNeumannEntropy}\left(rho\right) \land \left(0 \le \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(0\right)\right) \land \operatorname{vonNeumannEntropy}\left(rho\right) + \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(0\right)\right) = \operatorname{log}\left(d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/DualAccountFull.entropy_freedom_segment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eigenvalues of a density state form a probability distribution, and its von Neumann entropy is their Shannon entropy. The finite entropy bounds give zero at the lower end and log(d) at the upper end. The Gibbs identity supplies the complementary freedom. Thus any trajectory of density states lies on this segment point by point; no dynamical law or parametrization of time is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/DualAccountFull.dual_account_full`
- Truth anchor: `D5/S3/Quantum/Divergence/DualAccountFull.entropy_freedom_segment`
- Dependency: [D5/S3/Entropy/EntropyNonneg](../../Entropy/EntropyNonneg.md)
- Dependency: [D5/S3/Quantum/Divergence/GibbsVariationalIdentity](GibbsVariationalIdentity.md)
- Dependency: [D5/S3/Quantum/Sharpness/FreeNegentropyBudget](../Sharpness/FreeNegentropyBudget.md)
- Dependency: [D5/S3/Quantum/Tomography/MutuallyUnbiasedDiagonalPlanes](../Tomography/MutuallyUnbiasedDiagonalPlanes.md)
