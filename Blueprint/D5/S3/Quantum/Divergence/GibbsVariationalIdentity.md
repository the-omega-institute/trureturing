# Gibbs Variational Identity

## Abstract

The normalized matrix exponential gives an exact entropy decomposition.

Matrices are complex and indexed by an arbitrary finite nonempty type n. H is Hermitian. DensityState means a positive semidefinite matrix with complex trace one. ReTr is the real part of the matrix trace. partitionFunction(H) is ReTr(exp(H)) and is strictly positive; gibbsState(H) is its inverse scalar times exp(H), a positive definite density matrix. Every logarithm is natural and the matrix logarithm is Mathlib's spectral continuous functional calculus.

**Lemma 1.1 (Logarithm of the Gibbs state).**

$$\forall n \in FiniteNonemptyType, H \in \operatorname{HermitianMatrix}\left(n\right),\; \operatorname{log}\left(\operatorname{gibbsState}\left(H\right)\right) = H - \operatorname{log}\left(\operatorname{partitionFunction}\left(H\right)\right) \cdot I$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.log_gibbs_state` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The logarithm of a positive scalar multiple separates into a scalar logarithm and the matrix logarithm. The logarithm of the exponential of a Hermitian matrix is the original matrix.

**Theorem 1.2 (Gibbs entropy decomposition).**

$$\forall n \in FiniteNonemptyType, H \in \operatorname{HermitianMatrix}\left(n\right), rho \in \operatorname{DensityState}\left(n\right),\; \operatorname{log}\left(\operatorname{partitionFunction}\left(H\right)\right) = \operatorname{ReTr}\left(H \cdot rho\right) + \operatorname{vonNeumannEntropy}\left(rho\right) + \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(H\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbs_variational_identity` (`✓ std3`). ∎

*Citation.* John Goold, Marcus Huber, Arnau Riera, Lídia del Rio, Paul Skrzypczyk (2016). *The role of quantum information in thermodynamics — a topical review*. DOI: [10.1088/1751-8113/49/14/143001](https://doi.org/10.1088/1751-8113/49/14/143001).

*Commentary.*

Expanding relative entropy cancels the self-logarithm term against von Neumann entropy. Substitution of the Gibbs logarithm, trace normalization, and cyclicity of the trace give the equality. The density matrix may fail to commute with H.

**Theorem 1.3 (The maximally mixed reference state).**

$$\forall n \in FiniteNonemptyType, rho \in \operatorname{DensityState}\left(n\right),\; \operatorname{vonNeumannEntropy}\left(rho\right) + \operatorname{quantumRelativeEntropy}\left(rho, \operatorname{gibbsState}\left(0\right)\right) = \operatorname{log}\left(\operatorname{card}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.entropy_uniform_identity` (`✓ std3`). ∎

*Citation.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

At H = 0 the partition function is card(n), and gibbs_state_zero identifies the Gibbs matrix with I/card(n). Substitution into the general identity gives entropy plus relative entropy to the maximally mixed state equal to log(card(n)).

## References

- Truth anchor: `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.entropy_uniform_identity`
- Truth anchor: `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.gibbs_variational_identity`
- Truth anchor: `D5/S3/Quantum/Divergence/GibbsVariationalIdentity.log_gibbs_state`
- Dependency: [D5/S3/Quantum/Divergence/VonNeumannEntropyPinching](VonNeumannEntropyPinching.md)
