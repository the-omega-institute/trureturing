# A common pure extension for two Gaussian covariances

## Abstract

Coercivity, common pure Gaussian extension, and square-summable squeezing.

On a complex Hilbert space with a real conjugation, the reference covariance is the identity, the target covariance is Q, and R is their common real skew-adjoint operator. The Hilbert–Schmidt difference of the signed covariance square roots is the condition in Eq. (71) of Satishchandran and Sorce.

**Theorem 1.1 (Coercivity from a covariance root difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.covariance_coercive`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.covariance_coercive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive Q with trivial kernel, positive signed covariances, and a Hilbert–Schmidt root difference, Q differs from the identity by a Hilbert–Schmidt operator. The difference of squares factors through the root difference on both sides. The compact Fredholm alternative gives invertibility and positivity gives a strictly positive scalar lower bound. The positive square root is invertible, and both it and its inverse differ from the identity by Hilbert–Schmidt operators.

**Definition 1.2 (Normalized skew operator).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.normalizedSkew`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.normalizedSkew` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply R on both sides by the inverse of the positive covariance square root.

**Definition 1.3 (Positive defect root).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.defectRoot`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.defectRoot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the positive square root of one plus the square of the normalized skew operator.

**Theorem 1.4 (Signed roots and the defect contraction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.normalized_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.normalized_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For a real positive invertible covariance and real skew-adjoint R, positivity of the minus signed covariance gives a normalized skew contraction. Conjugation gives positivity of the plus signed operator. The two signed roots commute, their product is the defect root, and the latter is real and lies between zero and the identity.

**Theorem 1.5 (Hilbert–Schmidt defect difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.defectRoot_sub_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.defectRoot_sub_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Right multiplication by the inverse covariance root gives two operators with Hilbert–Schmidt difference. Their absolute values are the two normalized minus signed roots. The absolute-value estimate compares these roots. Conjugation compares the plus roots, and expansion of the difference of the two products gives the defect comparison.

**Definition 1.6 (Doubled covariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Conjugate one plus the defect root by the positive covariance root.

**Theorem 1.7 (Reference doubled covariance).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

At the identity covariance, the doubled covariance is one plus the positive square root of one plus the square of the original skew operator.

**Theorem 1.8 (Doubled covariance bounds and restriction).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The doubled covariance D is real and invertible and lies between Q and twice Q. The normalized skew operator commutes with the defect root. The product of one plus and one minus the defect is minus the square of the normalized skew operator. Consequently half of D minus R D inverse R is exactly Q.

**Theorem 1.9 (Hilbert–Schmidt doubling difference).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_sub_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_sub_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Hilbert–Schmidt comparison of the defect roots and of the positive covariance root with the identity implies Hilbert–Schmidt comparison of the doubled covariances.

**Definition 1.10 (Common real phase-space map).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.phaseEmbedding`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.phaseEmbedding` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Send a fixed real vector f to the pair (f, Rf) divided by the square root of two.

**Theorem 1.11 (Injective real phase-space map).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.phaseEmbedding_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.phaseEmbedding_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Equality of the first coordinates forces equality of the original vectors. The argument allows a kernel for the common skew operator.

**Definition 1.12 (Pure extension coordinates).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.pureExtension`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.pureExtension` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real-linear equivalence sends (p, v) to the positive square root of D applied to p minus the imaginary unit times the inverse root applied to v.

**Theorem 1.13 (Covariance of the embedded real data).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.pureExtension_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.pureExtension_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The inner product of the extended images of f and g is the original covariance pairing minus the imaginary unit times the pairing with R. The two cross terms agree by skew-adjointness. The diagonal terms combine using the doubled covariance identity.

**Definition 1.14 (Transition on the real coordinate).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.squeezeTransition`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.squeezeTransition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Multiply the positive target doubled root by the inverse of the positive reference doubled root.

**Theorem 1.15 (Transition metric).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.squeezeTransition_properties`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.squeezeTransition_properties` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For real positive invertible doubled covariances with Hilbert–Schmidt difference, the transition L is real and invertible. Its metric is bounded below by a positive multiple of the identity and its difference from the identity is real, self-adjoint, and Hilbert–Schmidt.

**Theorem 1.16 (Square-summable squeeze eigenbasis).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.exists_squeeze_eigenbasis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.exists_squeeze_eigenbasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

On a separable Hilbert space, restrict the metric perturbation to the fixed real subspace and diagonalize it as a compact self-adjoint operator. The logarithms of its shifted positive eigenvalues, divided by two, are square-summable. The squared norm of the transition of any vector is the sum over the complexified basis of its squared real coefficients weighted by exp(2r) and squared imaginary coefficients weighted by exp(-2r).

**Theorem 1.17 (Common pure Gaussian extension).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.commonPureExtension`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.commonPureExtension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

For positive Q with trivial kernel, positive signed covariances with Hilbert–Schmidt root difference determine two real-linear pure coordinates on the same doubled phase space. Their restrictions along the common embedding give the two original complex covariance pairings. The transition between the pure coordinates admits the countable squeeze expansion with square-summable squeeze parameters.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.commonPureExtension`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.covariance_coercive`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.defectRoot`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.defectRoot_sub_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_one`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_properties`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.doubleCovariance_sub_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.exists_squeeze_eigenbasis`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.normalizedSkew`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.normalized_properties`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.phaseEmbedding`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.phaseEmbedding_injective`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.pureExtension`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.pureExtension_inner`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.squeezeTransition`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension.squeezeTransition_properties`
- Dependency: [D5/S3/Quantum/Analysis/CompactEigenbasis](../CompactEigenbasis.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRAbsoluteValueHS](CCRAbsoluteValueHS.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation](CCRConjugation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/QuarterPowerSqrtHilbertSchmidt](QuarterPowerSqrtHilbertSchmidt.md)
- Dependency: [D5/S3/Quantum/Analysis/TraceClass/HilbertSchmidt](../TraceClass/HilbertSchmidt.md)
