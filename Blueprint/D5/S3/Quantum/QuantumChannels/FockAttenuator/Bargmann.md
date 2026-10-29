# Bargmann analysis on the completed Fock space

## Abstract

The completed occupation space has an injective entire Bargmann transform with Gaussian control on every bounded disk.

**Definition 1.1 (The completed transform).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.transform`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.transform` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H is lp over the natural numbers with complex coordinates and exponent two. The transform of a at z is the inner product of the exponential vector at conjugate z with a. The inner product is conjugate linear in its first argument. No finite support or energy assumption is imposed.

**Theorem 1.2 (An entire factorial series).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.has_fpower_series`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.has_fpower_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a in H, the full formal multilinear power series at zero has infinite radius and sums to the transform. Its coefficient of degree n is a(n) divided by sqrt(n!). This is a theorem about the actual completed vector.

**Theorem 1.3 (Entire evaluation).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.entire`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.entire` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transform of every completed vector is complex differentiable at every complex point. An arbitrary entire function is not thereby assigned a vector in H.

**Theorem 1.4 (Absolute radial control).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.tsum_radial_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.tsum_radial_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative real radius R, the sum over all n of norm(a(n))*R^n/sqrt(n!) is at most norm(a)*exp(R^2/2). The proof applies lp Holder to the actual exponential vector, whose squared norm is exp(R^2). The sum includes all coordinates, including at R=0.

**Theorem 1.5 (Recovery of every coordinate).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.injective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of two transforms as functions on the whole complex plane implies equality of their original H vectors. Uniqueness of the convergent power series recovers each factorial-normalized coordinate.

**Theorem 1.6 (Hilbert limits give local uniform limits).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.uniform_of_tendsto`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.uniform_of_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index type, every filter, every net u converging to a in the H norm, and every nonnegative radius R, the transforms of u converge uniformly to the transform of a on the closed disk of radius R. The Gaussian difference bound supplies one estimate for all points of that disk.

**Theorem 1.7 (Totalness in the completion).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.exponential_dense_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.exponential_dense_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The topological closure of the complex span of all actual exponential vectors is all of H. A vector in its orthogonal complement has zero transform and therefore every coordinate zero. This supplies the density used in the later coefficient-operator reconstruction; no assertion about entropy is made here.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.entire`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.exponential_dense_span`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.has_fpower_series`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.injective`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.transform`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.tsum_radial_le`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.uniform_of_tendsto`
- Dependency: [D5/S3/Quantum/QuantumChannels/FockAttenuator/BeamSplitter](BeamSplitter.md)
