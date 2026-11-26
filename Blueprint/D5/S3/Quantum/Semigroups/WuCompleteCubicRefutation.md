# The fixed-marginal cubic bound fails for a separable state

## Abstract

A faithful separable two-qubit state refutes the fixed-marginal tracial cubic bound.

Use the product basis 00, 01, 10, 11 with the system index first. Write R_A = Tr_B R and R_B = Tr_A R, D = I₂/2, σ = diag(2,26)/28, and T = D ⊗ R_B. The amplified jump is J = |0⟩⟨1| ⊗ I₂. With a = b = 1/2 the paired generator is L(Y) = 2a K(J,Y) + 2b K(J†,Y), where K(V,Y) = (V†VY + YV†V)/2 − V†YV.

In the ordinary-trace convention of Wu v1 (2.4), take s = 3 and its conjugate s′ = 3/2. Put p = 1/3, q = 2/3, and X_r = T^(−r/2) R^r T^(−r/2). Then E(R) = Re Tr[T^(1/2) X_q T^(1/2) L(X_p)]/(4pq) and H(R) = Re Tr[R(log R − log T)].

**Definition 1.1 (Proposed fixed-marginal extension).**

$$\forall R \in \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{C}\right),\; \operatorname{PosDef}\left(R\right) \Rightarrow \left(\left(\operatorname{Tr}_{B}\right)\left(R\right) = D \Rightarrow \left(\left(\operatorname{Tr}_{A}\right)\left(R\right) = \sigma \Rightarrow \left(\operatorname{Separable}\left(R\right) \Rightarrow \frac{\operatorname{H}\left(R\right)}{2} \le \operatorname{E}\left(R\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

This research claim proposes the ancillary extension of Wu v1 (3.54) with the sharp tracial coefficient 1/2 from (3.55) at β = 0. The joint state is faithful and separable across the system and ancilla, with R_A = D and R_B = σ. These marginals enforce trace one.

**Theorem 1.2 (A faithful separable counterexample).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jinsong Wu (2026). *Sharp Logarithmic Sobolev Inequalities for q-Araki-Woods Ornstein-Uhlenbeck Semigroups*. DOI: [10.48550/arXiv.2610.33686](https://doi.org/10.48550/arXiv.2610.33686). URL: <https://arxiv.org/abs/2610.33686v1>.

*Commentary.*

Take ρ with diagonal (2,26,2,26)/56 and symmetric 00,11 entries 5/56. All other off-diagonal entries vanish. Its spectrum is (1,26,2,27)/56 and its actual marginals are D and σ. It is a mixture of D ⊗ D with weight 4/56 and four rank-one product projectors with weight 13/56 each. Their local unit vectors are (1,z)/√2 and (1,5 overline(z))/√26 for z = 1, −1, i, −i.

The actual T commutes with J, so both T and I satisfy the modular relation with rate ratio a/b = 1. The spectral expansion in generatorTrace_eq_cosh uses the same eigenvalues of ρ, jump entries in its eigenbasis, and rates for both references. The embedded traces are therefore equal, so the energy can be evaluated with I. The entropy uses the actual T.

For x = 2^(1/3) and y = 26^(1/3), the finite certificate gives 56 E(ρ) = (9/8)[56 − (14x² + 17x + 38y² + 113y)/13] and 56 H(ρ) = 27 log 27 − 2 log 2 − 26 log 26. The rational cube-root bounds x > 12599/10000 and y > 29624/10000 and the log-series bounds log(3/2) ≥ 2/5, log 2 ≥ 56/81, and log(27/26) ≥ 2/53 give 56 E(ρ) < 7/5 < 28 H(ρ).

## References

- Truth anchor: `D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Semigroups/WuCompleteCubicRefutation.result`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/IptPptSquaredEquivalence](../QuantumChannels/IptPptSquaredEquivalence.md)
- Dependency: [D5/S3/Quantum/Semigroups/WuModularEdgeSpectral](WuModularEdgeSpectral.md)
