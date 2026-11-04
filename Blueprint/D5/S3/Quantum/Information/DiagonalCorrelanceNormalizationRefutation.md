# Diagonal correlance exceeds its proposed normalization

## Abstract

A seven-qubit diagonal state exceeds the proposed diagonal-correlance normalization.

**Definition 1.1 (The product of the one-coordinate reductions).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(p: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation.reductionProduct}\left(p\right): \operatorname{Matrix}\left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right), \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right), \mathbb{R}\right)\right) = \operatorname{Matrix.diagonal}\left(\left(\lambda \left(x: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \mapsto \left(\prod_{i: \operatorname{Fin}\left(n\right)} \left(\operatorname{FunOnFinite.map}\left(\left(\lambda \left(y: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \mapsto \left(y\left(i\right)\right)\right), p, x\left(i\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.reductionProduct` (`✓ std3`).

*Citation.* Samuel R. Hedemann (2020). *Correlance and discordance: computable measures of nonlocal correlation*. DOI: [10.1007/s11128-020-02676-8](https://doi.org/10.1007/s11128-020-02676-8). URL: <https://arxiv.org/abs/2001.03453v2>.

*Commentary.*

For a real function p on n-bit strings, the reduction product is the diagonal matrix whose entry at x is the product of the n one-coordinate marginals evaluated at x i. FunOnFinite.map sums p over the fiber of the coordinate map y to y i. When p is a probability distribution, these marginals are the diagonal entries of the single-qubit reduced states, and this matrix is their tensor product. This is the diagonal-state form of Hedemann's equation (11), CorrelanceAndDiscordance.tex lines 308-312. The definition also applies to arbitrary real p and to n equal to zero.

**Definition 1.2 (Raw correlance of a diagonal state).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(p: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation.correlanceRaw}\left(p\right): \mathbb{R}\right) = \operatorname{Matrix.trace}\left(\left(\operatorname{Matrix.diagonal}\left(p\right) - \operatorname{D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation.reductionProduct}\left(p\right)\right)^{\left(2: \mathbb{N}\right)}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.correlanceRaw` (`✓ std3`).

*Citation.* Samuel R. Hedemann (2020). *Correlance and discordance: computable measures of nonlocal correlation*. DOI: [10.1007/s11128-020-02676-8](https://doi.org/10.1007/s11128-020-02676-8). URL: <https://arxiv.org/abs/2001.03453v2>.

*Commentary.*

Raw correlance is the trace of the square of the difference between the diagonal matrix with entries p and its reduction product. For a probability distribution p, this is the squared Hilbert-Schmidt distance between the diagonal density matrix and the tensor product of its single-qubit reductions. It is Hedemann's equation (10), CorrelanceAndDiscordance.tex lines 303-305, restricted to diagonal real matrices. No probability assumption is needed to define it.

**Definition 1.3 (The proposed bound for every number of qubits).**

$$\left(\operatorname{D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation.claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\left(\left(2: \mathbb{N}\right) \le n\right) \Rightarrow \left(\forall \left(p: \left(\left(\operatorname{Fin}\left(n\right)\right) \to \left(\operatorname{Bool}\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.TotalVariation.CycleSingleCutMinimax.Probability}\left(p\right)\right) \Rightarrow \left(\operatorname{D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation.correlanceRaw}\left(p\right) \le \frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)} - \frac{\left(1: \mathbb{R}\right)}{\left(2: \mathbb{R}\right)^{n}}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Samuel R. Hedemann (2020). *Correlance and discordance: computable measures of nonlocal correlation*. DOI: [10.1007/s11128-020-02676-8](https://doi.org/10.1007/s11128-020-02676-8). URL: <https://arxiv.org/abs/2001.03453v2>.

*Commentary.*

The assertion requires the raw correlance of every probability distribution on n-bit strings to be at most one half minus the reciprocal of two to the nth power, for every natural n at least two. Probability p means that all entries are nonnegative and their finite sum is one. This is the qubit consequence of the maximum over all diagonal states in equation (16) and the normalization asserted in equation (18), CorrelanceAndDiscordance.tex lines 450-465. The source states that the equal mixture of the first and last basis projectors attains this maximum in all systems.

**Theorem 1.4 (A seven-qubit counterexample).**

$$\neg \left(\operatorname{D5.S3.Quantum.Information.DiagonalCorrelanceNormalizationRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hedemann-2020-diagonal-correlance-normalization` (refuted) by `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hedemann-2020-diagonal-correlance-normalization","declaration_gid":"D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Samuel R. Hedemann (2020). *Correlance and discordance: computable measures of nonlocal correlation*. DOI: [10.1007/s11128-020-02676-8](https://doi.org/10.1007/s11128-020-02676-8). URL: <https://arxiv.org/abs/2001.03453v2>.

*Commentary.*

Subtraction and squaring preserve diagonal matrices, and the trace of a diagonal matrix is the sum of its entries. Thus raw correlance is the sum over all bit strings x of the squared difference between p(x) and the product of its coordinate marginals at x.

For seven qubits, take p to put mass 3/5 on the all-false string, mass 2/5 on the all-true string, and zero elsewhere. These entries are nonnegative and sum to one. Summing over a coordinate fiber gives mass 3/5 at false and mass 2/5 at true, for every coordinate i. Consequently the reduction-product entry at x is the product of seven factors, each equal to 3/5 or 2/5 according to the bit x i.

Squaring this product squares each factor. The sum over all seven-bit strings then factors into seven copies of (3/5)^2 + (2/5)^2, so the sum of the squared reduction-product entries is (13/25)^7. The two constant strings are distinct, so the sum of p(x)^2 is just (3/5)^2 + (2/5)^2 = 13/25. The mixed sum of p(x) times the reduction-product entry has only the same two nonzero terms: (3/5)^8 + (2/5)^8.

Expanding each squared difference and distributing the finite sums therefore gives raw correlance 13/25 - 2((3/5)^8 + (2/5)^8) + (13/25)^7 = 3023545392/6103515625. If the assertion held, applying it to n = 7 and this probability distribution would bound that number by 1/2 - 1/2^7 = 63/128. Their difference is 2492325801/781250000000, which is strictly positive, a contradiction. Thus the proposed bound fails already for seven qubits. This does not determine the actual maximum over diagonal states.

## References

- Truth anchor: `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.correlanceRaw`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.reductionProduct`
- Truth anchor: `D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.result`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S3/TotalVariation/CycleSingleCutMinimax](../../TotalVariation/CycleSingleCutMinimax.md)
