# Restricting a random injective naming

## Abstract

The joint distribution of a fixed selection of yet unnamed vertices.

**Definition 1.1 (Mass of one uniform outcome).**

Lean statement: `D5/S3/Combinatorics/Probability/NamingRestrictionLaw.namingMass`

*Formalization.* `D5/S3/Combinatorics/Probability/NamingRestrictionLaw.namingMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The mass assigned to an outcome is the reciprocal of the cardinality of its naming space, represented in the extended nonnegative reals.

**Theorem 1.2 (Joint uniformity on the selected vertices).**

Lean statement: `D5/S3/Combinatorics/Probability/NamingRestrictionLaw.uniform_residual_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/NamingRestrictionLaw.uniform_residual_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix distinct names from a finite name set on a subset of a finite vertex set. Choose an available subset of names disjoint from the fixed names. Assume at least one injective completion exists whose remaining names are all available. Sample such a completion uniformly and restrict to a fixed injectively indexed selection of the remaining vertices.

Every injection from the selection into the available name set has mass equal to the reciprocal of the total number of such injections.

The consistent completions correspond to the residual injections. A permutation of the available names carrying one restricted naming to another gives a bijection of their completion fibers. The equal fiber masses sum to one.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/NamingRestrictionLaw.namingMass`
- Truth anchor: `D5/S3/Combinatorics/Probability/NamingRestrictionLaw.uniform_residual_restriction`
- Dependency: [D5/S3/Combinatorics/Probability/PartialNameAssignment](PartialNameAssignment.md)
