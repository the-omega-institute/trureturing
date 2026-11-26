# Joint law of a reply and its naming completion

## Abstract

Sampling an ordered reply and then completing the naming preserves the joint law.

**Definition 1.1 (Vertices named after the request).**

Lean statement: `D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.namedAfter`

*Formalization.* `D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.namedAfter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the union of the vertices with fixed names and the range of the request.

**Theorem 1.2 (Read the reply before completing the naming).**

Lean statement: `D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.joint_ordered_reply_completion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.joint_ordered_reply_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an injective partial naming of a finite vertex set with names from a finite name set. Choose an available subset disjoint from the fixed names and assume there is a completion that uses those names on the remaining vertices. Fix a request with one vertex at each position. The complete-naming experiment samples a completion uniformly and then reads the requested names.

The marginal law puts zero mass on inconsistent replies. Each consistent reply has mass equal to the reciprocal of the number of injections from the distinct fresh requested vertices into the available names.

For each reply of positive mass there is an expanded partial injective naming that returns the prescribed name at every request position. The completion kernel at that reply samples uniformly from its compatible full namings, using the remaining available names outside the expanded domain. Drawing a reply and then using this kernel has the same joint law of the reply and the full naming as the complete-naming experiment.

The observed reply fixes the restriction to the union of old and requested vertices. Name agreement on this union is precisely the observation fiber. Disintegrating the original law over these fibers preserves the paired outcome, and the uniform conditional completion law identifies the concrete kernel.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.joint_ordered_reply_completion`
- Truth anchor: `D5/S3/Combinatorics/Probability/JointNamingReplyCompletion.namedAfter`
- Dependency: [D5/S3/Combinatorics/Probability/NamingUpdate](NamingUpdate.md)
- Dependency: [D5/S3/Combinatorics/Probability/OrderedNamingReply](OrderedNamingReply.md)
