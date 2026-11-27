# Updating a partially observed naming

## Abstract

A finite random injective naming can be conditioned on additional assigned names.

**Definition 1.1 (The remaining available names).**

Lean statement: `D5/S3/Combinatorics/Probability/NamingUpdate.unused`

*Formalization.* `D5/S3/Combinatorics/Probability/NamingUpdate.unused` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Remove the values of the expanded naming from the original available set.

**Definition 1.2 (Agreement with an expanded assignment).**

Lean statement: `D5/S3/Combinatorics/Probability/NamingUpdate.agrees`

*Formalization.* `D5/S3/Combinatorics/Probability/NamingUpdate.agrees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A full injective naming agrees with the assigned value at each vertex of the expanded assignment.

**Theorem 1.3 (The remaining completions have a uniform conditional law).**

Lean statement: `D5/S3/Combinatorics/Probability/NamingUpdate.uniform_after_reveal`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/NamingUpdate.uniform_after_reveal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix finite vertex and name sets. An initial injective assignment names some vertices, and the other vertices use the available names. Take an expanded injective assignment on a superset of the initially named vertices. It extends the fixed names and uses available names on the newly assigned vertices. Assume an original completion agrees with the expanded assignment.

The agreeing original completions correspond bijectively to the completions of the expanded assignment using the remaining names. The correspondence preserves the full naming. Filtering the uniform original law on agreement and forgetting the completion condition gives the same distribution as forgetting the condition on the uniform new law.

Every agreeing injection avoids the newly fixed values away from the expanded domain. Conversely a new completion satisfies the original assignment and availability requirements. The two uniform laws agree after transport by this bijection.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/NamingUpdate.agrees`
- Truth anchor: `D5/S3/Combinatorics/Probability/NamingUpdate.uniform_after_reveal`
- Truth anchor: `D5/S3/Combinatorics/Probability/NamingUpdate.unused`
- Dependency: [D5/S3/Combinatorics/Probability/PartialNameAssignment](PartialNameAssignment.md)
