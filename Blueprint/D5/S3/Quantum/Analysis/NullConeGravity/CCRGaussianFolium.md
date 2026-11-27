# Gaussian folium sufficiency

## Abstract

Folium sufficiency for comparable Gaussian CCR states, including degenerate symplectic forms.

Work with a Weyl system whose complex linear span is norm dense and two normalized positive Gaussian functionals. The real datum map takes values in the fixed space of a conjugation on a separable complex Hilbert space. The reference symmetric covariance is the identity, the target covariance Q is positive and injective, and the common skew operator R commutes with conjugation. Both signed covariance operators are positive.

**Definition 1.1 (Inclusion of the fixed real form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.fixedInclusion`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.fixedInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The real-linear inclusion sends the fixed real subspace into the original Hilbert space.

**Definition 1.2 (Real covariance form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.realCovariance`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.realCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take the real part of the operator inner product on two fixed real vectors.

**Definition 1.3 (Real symplectic form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.realSymplecticForm`

*Formalization.* `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.realSymplecticForm` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Take minus twice the real part of the skew operator inner product on fixed real vectors.

**Theorem 1.4 (Totality of the fixed real form).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.fixedInclusion_dense`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.fixedInclusion_dense` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Every vector is a sum of a fixed real vector and the imaginary multiple of another, so the complex span of the fixed real form contains the whole Hilbert space.

**Theorem 1.5 (Phase and norm of pure coordinates).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.extensionPhaseNorm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.extensionPhaseNorm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

The signed inner product identity on fixed real vectors gives the common symplectic phase and the required covariance norm square when both operators commute with conjugation.

**Theorem 1.6 (Mutual Gaussian excitability).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.gaussian_mutual_excitable_of_sqrt_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.gaussian_mutual_excitable_of_sqrt_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

A Hilbert–Schmidt difference of the signed covariance square roots implies both inclusions of vector folia. The common pure extension realizes the two signed covariances on a common real phase space. The Hilbert–Schmidt difference of the doubled covariances admits square-summable squeeze parameters in either order. For each direction, the squeezed vector is transported to a Hilbert basis split across the closed complex span of the embedded data and its orthogonal complement. Occupation splitting gives a countable family of vectors in the first Fock space with squared norms summing to one and Weyl matrix coefficients summing to the target characteristic function. Gram equality of cyclic Weyl vectors and coherent totality give the intertwining unitary from the reference GNS space. The basis split and enumeration also apply to finite or empty basis sets. The resulting vectors therefore realize excitability on the full algebra, including a nontrivial symplectic radical.

**Theorem 1.7 (Gaussian folium sufficiency).**

Lean statement: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.gaussian_excitable_of_sqrt_hs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.gaussian_excitable_of_sqrt_hs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gautam Satishchandran and Jonathan Sorce (2026). *Uniqueness of null-local modular flow*. DOI: [10.48550/arXiv.2607.20678](https://doi.org/10.48550/arXiv.2607.20678). URL: <https://arxiv.org/html/2607.20678v1>.

*Commentary.*

Under the same covariance, characteristic-function and Hilbert–Schmidt hypotheses, the target state is excitable in the reference GNS representation.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.extensionPhaseNorm`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.fixedInclusion`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.fixedInclusion_dense`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.gaussian_excitable_of_sqrt_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.gaussian_mutual_excitable_of_sqrt_hs`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.realCovariance`
- Truth anchor: `D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianFolium.realSymplecticForm`
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRConjugation](CCRConjugation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockOccupation](CCRFockOccupation.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRFockWeyl](CCRFockWeyl.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRGaussianExtension](CCRGaussianExtension.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeInfinite](CCRSqueezeInfinite.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/CCRWeylState](CCRWeylState.md)
- Dependency: [D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondEq71Trace4D](NullDiamondEq71Trace4D.md)
