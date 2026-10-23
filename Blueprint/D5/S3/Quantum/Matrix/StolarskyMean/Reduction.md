# Stolarsky logarithmic coordinates

## Abstract

Homogeneous Stolarsky profiles and logarithmic reconstruction.

**Definition 1.1 (The exponential profile).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.psi`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Evaluate the Stolarsky mean on exp(-t) and exp(t). The definition includes all continuous parameter extensions and the value at zero.

**Definition 1.2 (The second derivative defect).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.f`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.f` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the profile from its second ordinary real derivative. Derivatives are the total derivative operations supplied by Lean.

**Theorem 1.3 (Symmetry).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_symm`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_symm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Stolarsky mean is symmetric in its two arguments, at every real parameter and for the total real definition.

**Theorem 1.4 (Positive homogeneity).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_homogeneous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_homogeneous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive a, b, and c, scaling both inputs by c scales the Stolarsky mean by c. This includes the logarithmic and identric branches.

**Theorem 1.5 (Positive entries).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every parameter at least two, a positive pair has strictly positive Stolarsky mean. Strict monotonicity of real powers gives the sign of the divided difference.

**Definition 1.6 (The homogeneous logarithmic kernel).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.profileKernel`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.profileKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the profile at half the difference of the input logarithms by the product of the input square roots.

**Theorem 1.7 (Recovering the mean from its profile).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_eq_profileKernel`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_eq_profileKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive inputs, every real Stolarsky parameter agrees with the homogeneous logarithmic kernel of its exponential profile.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.f`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.profileKernel`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.psi`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_eq_profileKernel`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_homogeneous`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_pos`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Reduction.stolarsky_symm`
- Dependency: [D5/S3/Quantum/Matrix/StolarskyMean/Spectral](Spectral.md)
- Dependency: [D5/S3/Weil/ZetaLinear/FiniteInversePoissonCriterion](../../../Weil/ZetaLinear/FiniteInversePoissonCriterion.md)
