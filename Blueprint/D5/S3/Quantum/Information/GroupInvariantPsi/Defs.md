# Tensor averages and asymptotic overlaps

## Abstract

Finite-group discrimination of faithful density matrices.

**Definition 1.1 (Tensor coordinates).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.tensorPower`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.tensorPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Words of length n index the tensor basis. The entry at two words is the product of the corresponding one-site matrix entries; the empty tensor has its single entry equal to one.

**Definition 1.2 (Uniform conjugation average).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.twirlPower`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.twirlPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a unitary representation of a finite group, average the conjugates of the tensor density matrix by the tensor representation with weight one divided by the group cardinality.

**Definition 1.3 (Finite tensor overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.psiN`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.psiN` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real part of the trace of the product of the real spectral powers with exponents s and one minus s, and then its real logarithm. Spectral powers use the continuous functional calculus.

**Definition 1.4 (Asymptotic overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.psi`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected limit of the finite tensor overlap divided by the tensor length is used together with an explicit convergence hypothesis.

**Definition 1.5 (Differentiability assertion).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.claim`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every dimension, finite group and unitary representation, and every pair of positive definite complex matrices of trace one, convergence at every parameter strictly between zero and one is asserted to imply differentiability throughout that interval. Finite groups carry the discrete compact topology, and their normalized Haar measure is uniform. A failure in this domain therefore also gives a failure for compact groups.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.claim`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.psi`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.psiN`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.tensorPower`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Defs.twirlPower`
- Dependency: [D5/S3/Quantum/Matrix/SpectralPower](../../Matrix/SpectralPower.md)
- Dependency: [D5/S3/Quantum/Recovery/PurifiedLocalPath](../../Recovery/PurifiedLocalPath.md)
