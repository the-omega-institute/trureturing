# The law of an ordered naming reply

## Abstract

The exact distribution of ordered answers under a uniform injective naming.

**Definition 1.1 (Distinct requested vertices without fixed names).**

Lean statement: `D5/S3/Combinatorics/Probability/OrderedNamingReply.FreshVertices`

*Formalization.* `D5/S3/Combinatorics/Probability/OrderedNamingReply.FreshVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the vertices in the range of the request that lie outside the set with fixed names. Several request positions can select the same vertex.

**Definition 1.2 (Consistency of a reply).**

Lean statement: `D5/S3/Combinatorics/Probability/OrderedNamingReply.IsConsistentReply`

*Formalization.* `D5/S3/Combinatorics/Probability/OrderedNamingReply.IsConsistentReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A consistent reply returns each fixed name at every position selecting its vertex and chooses an available name for each remaining position. Two positions have the same returned name exactly when they select the same vertex.

**Theorem 1.3 (Mass of an ordered reply).**

Lean statement: `D5/S3/Combinatorics/Probability/OrderedNamingReply.ordered_reply_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/OrderedNamingReply.ordered_reply_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a partial injective naming of a finite vertex set with names from a finite name set. Choose an available set of names disjoint from the fixed names and assume there is at least one injective completion using only available names for vertices without a fixed name. Sample a completion uniformly and return the names at the vertices selected by the fixed request.

A consistent reply has mass equal to the reciprocal of the number of injections from the distinct requested vertices without fixed names into the available names. An inconsistent reply has zero mass.

Each consistent reply reconstructs a unique injection of the distinct requested vertices without fixed names. Choosing a request position for a vertex recovers its name, and the equality pattern makes the choice immaterial. The uniform law on these injections gives the exact mass through this correspondence.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/OrderedNamingReply.FreshVertices`
- Truth anchor: `D5/S3/Combinatorics/Probability/OrderedNamingReply.IsConsistentReply`
- Truth anchor: `D5/S3/Combinatorics/Probability/OrderedNamingReply.ordered_reply_mass`
- Dependency: [D5/S3/Combinatorics/Probability/NamingRestrictionLaw](NamingRestrictionLaw.md)
