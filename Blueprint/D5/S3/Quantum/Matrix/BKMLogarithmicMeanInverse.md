# Inverse of the BKM logarithmic mean

## Abstract

The matrix power integral and the resolvent logarithmic derivative are inverse complex-linear maps, also on every unital star-subalgebra containing the base.

**Theorem 1.1 (Both inverse identities).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.inverse_identities`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.inverse_identities` (`✓ std3`). ∎

*Citation.* Fumio Hiai; Hideki Kosaki; Dénes Petz; Mary Beth Ruskai (2013). *Families of completely positive maps associated with monotone metrics*. URL: <https://arxiv.org/abs/1212.1337v3>.

*Commentary.*

In the spectral basis of the positive definite matrix D, the actual power integral multiplies entry (i,j) by the logarithmic mean of the corresponding eigenvalues. The actual resolvent integral multiplies by its reciprocal. The mean equals the common positive eigenvalue when the eigenvalues coincide. Cancellation works entrywise for every complex matrix. Hiai, Kosaki, Petz, and Ruskai give the inverse pair in equations (1.1)–(1.2) and Appendix C.2.

**Definition 1.2 (Complex-linear equivalence).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv`

*Formalization.* `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Hideki Kosaki; Dénes Petz; Mary Beth Ruskai (2013). *Families of completely positive maps associated with monotone metrics*. URL: <https://arxiv.org/abs/1212.1337v3>.

*Commentary.*

The derivative of the matrix exponential at log D acts by the actual power integral. The inverse identities make this map bijective.

**Theorem 1.3 (Power-integral action).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv_apply` (`✓ std3`). ∎

*Citation.* Fumio Hiai; Hideki Kosaki; Dénes Petz; Mary Beth Ruskai (2013). *Families of completely positive maps associated with monotone metrics*. URL: <https://arxiv.org/abs/1212.1337v3>.

*Commentary.*

The forward map on the full matrix space is the power integral in equation (1.2).

**Theorem 1.4 (Resolvent action).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv_symm_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv_symm_apply` (`✓ std3`). ∎

*Citation.* Fumio Hiai; Hideki Kosaki; Dénes Petz; Mary Beth Ruskai (2013). *Families of completely positive maps associated with monotone metrics*. URL: <https://arxiv.org/abs/1212.1337v3>.

*Commentary.*

The inverse on the full matrix space is the resolvent integral in equation (1.1).

**Definition 1.5 (Automorphism of a star-subalgebra).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict`

*Formalization.* `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real powers lie in the unital star-subalgebra containing D by continuous functional calculus. Its closed complex subspace contains the average. Injectivity and finite dimension give surjectivity.

**Theorem 1.6 (Restriction of the power integral).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The restricted forward map agrees with the matrix power integral after inclusion.

**Theorem 1.7 (Restriction of the resolvent integral).**

Lean statement: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict_symm_apply`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict_symm_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Uniqueness of the ambient inverse identifies the restricted inverse with the actual resolvent logarithmic derivative on every complex subalgebra element.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.inverse_identities`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaEquiv_symm_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict_apply`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse.omegaRestrict_symm_apply`
- Dependency: [D5/S3/Quantum/Recovery/BKMMetricAdjointOrderObstruction](../Recovery/BKMMetricAdjointOrderObstruction.md)
