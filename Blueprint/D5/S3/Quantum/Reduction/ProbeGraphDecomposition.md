# ProbeGraphDecomposition

## Abstract

Finite dimension bounds the number of orthogonal nonorthogonality components of an arbitrary unit probe family.

The family index type may be infinite. Taking the equivalence closure of nonzero overlaps defines its actual components. One representative from each component is an orthonormal family, hence a linearly independent family in the same finite Hilbert space. Finite dimensionality therefore proves that the component quotient is finite. Distinct component spans are orthogonal because an overlap between their generators would merge the classes. If the original family spans the space, their orthogonal spans exhaust it.

**Theorem 1.1 (components finite).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_finite`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The quotient of any family of unit probes by the nonorthogonality component relation is finite.

**Theorem 1.2 (components orthogonal).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_orthogonal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_orthogonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

The actual Hilbert spans of distinct components are orthogonal.

**Theorem 1.3 (components span).**

Lean statement: `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_span`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Karl Mayer and Emanuel Knill (2018). *Quantum process fidelity bounds from sets of input states*. URL: <https://arxiv.org/html/1805.04491v1>.

*Commentary.*

When the original arbitrary probe family has full complex span, the supremum of its component Hilbert subspaces is the full space.

## References

- Truth anchor: `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_finite`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_orthogonal`
- Truth anchor: `D5/S3/Quantum/Reduction/ProbeGraphDecomposition.components_span`
- Dependency: [D5/S3/Quantum/Reduction/ProbeComponentRigidity](ProbeComponentRigidity.md)
