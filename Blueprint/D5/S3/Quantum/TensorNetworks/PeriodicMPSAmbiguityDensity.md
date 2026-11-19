# Sharp phase recovery on the periodic image

## Abstract

Complex-Zariski density of two-site collisions and sharp three-site recovery.

**Theorem 1.1 (Polynomial vanishing on actual collisions).**

$$\forall r \in Nat,\; \forall P \in MvPolynomial\left(Word\left(r + 4\right), Complex\right),\; \left(\forall A \in Fin\left(2\right) \to Bond,\; \forall B \in Fin\left(2\right) \to Bond,\; rank\left(twoFlattening\left(A, r\right)\right) = 4 \Rightarrow \left(rawTwo\left(B, r\right) = rawTwo\left(A, r\right) \Rightarrow \left(\left(\forall c \in Complex,\; gamma\left(B, r + 4, 1\right) \ne smul\left(c, gamma\left(A, r + 4, 1\right)\right)\right) \Rightarrow eval\left(traceWord\left(2, 2, r + 4, A\right), P\right) = 0\right)\right)\right) \Rightarrow \left(\forall A \in Fin\left(2\right) \to Bond,\; eval\left(traceWord\left(2, 2, r + 4, A\right), P\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.actual_collision_polynomial_vanishing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every r, every complex coordinate polynomial vanishing on all rank-four targets of nonproportional two-site collisions vanishes throughout the length r+4 trace-word image.

The parity parameters give a nonempty ordinary open set of collisions. Unitary physical basis changes preserve the whole collision. Starting from this unitary invariance, singular value decomposition reduces polynomial continuation to varying two diagonal entries successively on the unit circle. Finite roots extend each entry to the complex plane.

On a nonempty open set of shared pairs, change physical generators so that the second is traceless and its trace pairing with the first vanishes. The centered first matrix anticommutes with the second, which exchanges its two eigenlines. Rescaling their bases gives the diagonal and symmetric off-diagonal parity presentation. Trace is invariant under this virtual similarity. Polynomial continuation in all eight complex entries gives the full-image vanishing conclusion.

**Theorem 1.2 (Two-site ambiguity on every nonempty principal open).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.two_vs_three_phase_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.two_vs_three_phase_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Each nonempty principal complex-Zariski open contains a rank-four actual target with a nonproportional competitor of equal raw two-site density. At every rank-four target, equality of raw three-site density is equivalent to a unit-phase relation.

**Theorem 1.3 (A nonempty principal open for three-site recovery).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.three_site_recovery_principal_open`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.three_site_recovery_principal_open` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Fix a right inverse of a rank-four witness's flattening. The determinant of a variable flattening multiplied by that constant right inverse is a coordinate polynomial. At the witness it equals one, and on its nonvanishing locus the flattening has rank four, so the three-site phase theorem applies.

**Theorem 1.4 (Transport to the unit-mass slice).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.normalize_two_site_collision`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.normalize_two_site_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The trace of the common raw two-site Gram is the positive squared mass. A common scaling of the shared cores by a length-root of the inverse square root of that mass makes the raw trace one. Both marginals remain equal and cancellation preserves the absence of a global scalar.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.actual_collision_polynomial_vanishing`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.normalize_two_site_collision`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.three_site_recovery_principal_open`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPSAmbiguityDensity.two_vs_three_phase_recovery`
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPSTwoSiteAmbiguity](PeriodicMPSTwoSiteAmbiguity.md)
