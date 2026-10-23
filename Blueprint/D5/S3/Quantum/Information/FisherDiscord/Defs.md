# Fisher discord conventions

## Abstract

Finite matrix definitions for Fisher discord and partial trace.

**Definition 1.1 (Density matrices).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Defs.IsDensity`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Defs.IsDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A density matrix is positive semidefinite and has trace one.

Partial trace sums the matrix entries with identical second coordinates.

**Definition 1.2 (Local observables).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Defs.liftLeft`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Defs.liftLeft` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observable on the first factor is tensored with the identity on the second factor.

**Definition 1.3 (Symmetric logarithmic derivatives).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Defs.IsSLD`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Defs.IsSLD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Hermitian matrix L is a symmetric logarithmic derivative when i(rho H-H rho)=(L rho+rho L)/2.

**Definition 1.4 (Fisher information).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Defs.fisherSLD`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Defs.fisherSLD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The normalization is one quarter of the real part of trace(rho L L). The spectral formula establishes independence from the chosen Hermitian solution.

**Definition 1.5 (Skew information).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Defs.skewWY`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Defs.skewWY` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Skew information is minus one half the real trace of the square of the commutator between the positive matrix square root and the observable.

**Definition 1.6 (Partial trace comparison).**

Lean statement: `D5/S3/Quantum/Information/FisherDiscord/Defs.claim`

*Formalization.* `D5/S3/Quantum/Information/FisherDiscord/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The comparison quantifies over all finite dimensions, joint density matrices, Hermitian local observables and Hermitian SLD solutions on both spaces. Fisher discord is Fisher information minus skew information.

## References

- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Defs.IsDensity`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Defs.IsSLD`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Defs.claim`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Defs.fisherSLD`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Defs.liftLeft`
- Truth anchor: `D5/S3/Quantum/Information/FisherDiscord/Defs.skewWY`
