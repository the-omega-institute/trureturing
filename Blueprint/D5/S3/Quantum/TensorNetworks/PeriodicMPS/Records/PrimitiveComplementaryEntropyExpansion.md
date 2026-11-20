# Complementary conditional entropy of the primitive periodic collision

## Abstract

Complementary conditional entropy of the primitive periodic collision.

**Definition 1.1 (Spectral entropy in nats).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.matrixEntropy`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.matrixEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

The repository function sums −x log x over the real parts of the characteristic roots with multiplicities. On a density matrix these are its eigenvalues. The logarithm is natural and a zero eigenvalue contributes zero.

**Theorem 1.2 (Agreement with trace-log entropy).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.matrixEntropy_eq_density`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.matrixEntropy_eq_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For every finite density state the spectral sum agrees with the finite-state von Neumann entropy −Re tr(P log P), including singular P.

**Definition 1.3 (The literal complementary conditional entropy).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionComplementaryEntropy`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionComplementaryEntropy` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

Let m count the hidden sites and let n = 2 + m. The normalized amplitude flattening Wᵦ has rows on the first two sites and columns on the last m sites. The literal complementary density is Eᵦ = (Wᵦ†Wᵦ)ᵀ in the amplitude basis. For m ≥ 5 the fair classical–quantum state has diagonal blocks E₀/2 and E₁/2. Conditioning the label B on the last m sites gives H(B|E) = S(BE) − S(E), where the environment marginal is (E₀ + E₁)/2.

**Definition 1.4 (The eight-dimensional block Gram).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionGram`

*Formalization.* `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionGram` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

With R the common two-site density, G(Z) is half the block matrix with R on both diagonals, Z in the upper-right block and Z† in the lower-left block.

**Theorem 1.5 (Exact reduction to two block Grams).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionComplementaryEntropy_eq_gram`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionComplementaryEntropy_eq_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For every m ≥ 5, H(B|E) = S(G(0)) − S(G(Sₙ)), where Sₙ = W₀W₁† in the ket-first convention. Rectangular Gram matrices share their nonzero eigenvalues with multiplicity, and transpose preserves the characteristic roots.

**Theorem 1.6 (Uniform bound on the subdominant cross entries).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_cross_exponential_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_cross_exponential_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

One nonnegative constant C bounds every visible entry of Sₙ − γⁿS★ by Cβⁿ in absolute value, where γ = (1+i)(3+√41)/√200, S★ is the exact leading matrix, β = 8/√200 and n = 2 + m.

**Theorem 1.7 (The subdominant rate lies below the entropy scale).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionBeta_lt_alpha_sq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionBeta_lt_alpha_sq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The rate β is strictly smaller than α², where α = |γ| = (3+√41)/10.

**Theorem 1.8 (Entropy error from replacing the actual cross block).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_entropy_replacement_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_entropy_replacement_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For all sufficiently large m the absolute difference between S(G(Sₙ)) and S(G(αⁿS★)) is at most Kβⁿ for a nonnegative constant K. The phase of γⁿ is removed by block-unitary conjugation. A local eigenvalue perturbation bound at the positive definite G(0) controls the entropy difference.

**Theorem 1.9 (Quadratic entropy of the leading Gram path).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_commuting_entropy_quadratic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_commuting_entropy_quadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

As real t tends to zero through nonzero values, [S(G(0)) − S(G(tS★))]/t² tends to (310625−46875√41)/16384. The Hermitian slope commutes with G(0), so the path reduces to scalar expansions of −x log x.

**Theorem 1.10 (Exact coefficient of the complementary conditional entropy).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_complementary_entropy_asymptotic`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_complementary_entropy_asymptotic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Acknowledgement.* John Watrous (2018). *The Theory of Quantum Information — spectral calculus, reductions and entropy*. URL: <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>.

*Commentary.*

For the fair label conditioned on the literal complementary partial trace, H(B|E)/α^(2n) tends to (310625−46875√41)/16384 as m tends to infinity, with n = 2 + m. The coefficient uses natural-log entropy.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionBeta_lt_alpha_sq`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionComplementaryEntropy`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionComplementaryEntropy_eq_gram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collisionGram`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_commuting_entropy_quadratic`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_complementary_entropy_asymptotic`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_cross_exponential_remainder`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.collision_entropy_replacement_bound`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.matrixEntropy`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveComplementaryEntropyExpansion.matrixEntropy_eq_density`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveHiddenLabelEntropy](PrimitiveHiddenLabelEntropy.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Records/PrimitiveRecordLeadingCoefficient](PrimitiveRecordLeadingCoefficient.md)
- Dependency: [D5/S3/SpectralTopology/HermitianEigenvaluePerturbation](../../../../SpectralTopology/HermitianEigenvaluePerturbation.md)
