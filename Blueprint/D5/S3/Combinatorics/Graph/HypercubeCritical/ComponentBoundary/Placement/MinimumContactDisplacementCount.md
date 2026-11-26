# Three extensions give a sharp displacement count

## Abstract

Counting uniform displacement families from their extensions.

**Theorem 1.1 (The minimum size and its equality case).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount.card_and_eq_powerset_of_three_extensions`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount.card_and_eq_powerset_of_three_extensions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let each member of a nonempty family have d axes, with d positive. Suppose each set obtained by deleting one axis extends to at least three members of the family. Then at least (d + 2) choose 2 members occur. Equality gives all the d-subsets of one set of d + 2 axes.

The family of members containing a given axis, with that axis removed, inherits the extension hypothesis. Induction bounds every nonempty such family. A single ridge and its three extensions already use d + 2 axes. Count the incidences between all used axes and family members to obtain the lower bound. In the equality case there are exactly d + 2 used axes, and the family fills their d-subsets.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/MinimumContactDisplacementCount.card_and_eq_powerset_of_three_extensions`
