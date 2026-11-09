# Projectivity and a Finite Trivial Subgroup

## Abstract

Finite trivial subgroups obstruct projectivity through the group order.

**Theorem 1.1 (A finite trivial subgroup has unit cardinal).**

Lean statement: `D5/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder.isUnit_natCard_of_projective_of_isTrivial`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder.isUnit_natCard_of_projective_of_isTrivial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k be a field, G an arbitrary group, and rho a nonzero k-representation on V. If a finite subgroup H acts trivially and rho.asModule is projective over k[G], then the cardinality of H is a unit in k. The field, group, and representation universes remain independent; only H is finite.

Restriction preserves projective objects. A nonzero vector and a dual functional with value one split the trivial one-dimensional representation off the restricted representation. Projectivity therefore lifts the augmentation k[H] to an H-invariant element. Invariance makes every coefficient equal, while augmentation evaluates the coefficient sum as the cardinality of H times that common coefficient. Thus the subgroup order cannot vanish in the coefficient field.

This is the reusable group-action obstruction for later modular Frobenius applications. It supplies a necessary characteristic obstruction only; it does not assert a converse or a compiled finite-field example.

## References

- Truth anchor: `D5/S3/FiniteGroups/GroupAlgebra/ProjectiveKernelOrder.isUnit_natCard_of_projective_of_isTrivial`
