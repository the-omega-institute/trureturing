# Classical finite mixtures

## Abstract

Diagonal tensor states under permutation representations.

**Definition 1.1 (Permutation representation).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.permutationRepresentation`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.permutationRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A group action on basis labels gives a unitary representation by the inverse permutation matrices. This convention sends a diagonal entry at a label to the entry at its inverse image.

**Definition 1.2 (Word probabilities).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.mixtureWeight`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.mixtureWeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each word, average over the group the product of its one-site probabilities evaluated at inverse images of its labels.

**Definition 1.3 (Classical overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.mixtureTrace`

*Formalization.* `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.mixtureTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum over all words the product of the first mixture probability to power s and the second mixture probability to power one minus s.

**Theorem 1.4 (Diagonal tensor average).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.twirlPower_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.twirlPower_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite group acting on the basis labels, the uniform tensor twirl of a real diagonal matrix equals the diagonal matrix of the classical word mixture. Tensor permutation matrices reindex both matrix coordinates. Their diagonal tensor entries are products of one-site entries, so averaging gives the stated word probabilities, including tensor length zero.

**Theorem 1.5 (Spectral trace overlap).**

Lean statement: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.trace_pow_diag`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.trace_pow_diag` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real part of the trace of the product of the CFC powers of two real diagonal matrices is the sum of the corresponding products of scalar real powers. The existing diagonal functional-calculus theorem supplies both powers.

## References

- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.mixtureTrace`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.mixtureWeight`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.permutationRepresentation`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.trace_pow_diag`
- Truth anchor: `D5/S3/Quantum/Information/GroupInvariantPsi/Mixture.twirlPower_diag`
- Dependency: [D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity](../../Dynamics/EntropyProductionCoherenceDeletionIdentity.md)
- Dependency: [D5/S3/Quantum/Information/GroupInvariantPsi/Defs](Defs.md)
