# Incidence on a cut circle

## Abstract

Integration of edge values on a cyclic group with a vertex removed.

**Definition 1.1 (Induced directed edges).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.Edges`

*Formalization.* `D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.Edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An edge starts at a vertex in S and ends at its translate by a, also in S.

**Theorem 1.2 (Every edge assignment integrates).**

Lean statement: `D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.cycle_incidence_surjective`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.cycle_incidence_surjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any positive modulus, a proper vertex subset, a unit step, and an abelian group of edge values, the vertex-difference map is surjective.

Choose a missing vertex o. The coordinate of x is the least nonnegative residue of (x-o)/a. Along an induced edge that coordinate increases by exactly one, because its endpoint cannot be o. The negative cumulative sum of extended edge values therefore has the prescribed difference at every induced edge. No assumption about an existing inverse is used.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.Edges`
- Truth anchor: `D5/S3/Quantum/Tomography/Hadamard/BanicaCycleForestIncidence.cycle_incidence_surjective`
