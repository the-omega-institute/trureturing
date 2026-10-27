# Positive runs in every actual reduced core

## Abstract

Positive runs in every actual reduced core.

The source object is the complete integer height function on the full rectangular grid. Residual retains unit-edge differences, normalization, the exact separate strict minimum and maximum counts, and failure of a single common physical side for all minima. The Core family is unchanged: both dimensions are less than twice the total extremum count, and each full normalized core has no adjacent frozen lines and positive frozen-run counts on both axes.

**Theorem 1.1 (Every large residual array reaches a positive-run Core).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraPartitionCore.residual_core_exists`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraPartitionCore.residual_core_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive natural a and b with a+b at least five, any dimensions m,n at least 2(a+b)-1, and every actual Residual a b array h on those dimensions, there exists K in Core a b such that JointReduction h K holds and, separately for each of the four physical sides, all minima lie on that side before reduction if and only if they do afterwards. The reduced core is the complete existing function at its own exact dimensions.

Each large dimension exceeds a+b, whereas the number of occupied lines is at most the total number of extrema, which is at most a+b. Thus both axes have a genuine frozen line. Legal same-axis deletion leaves a frozen line, and orthogonal deletion preserves the other frozen witness. The existing reduced-core inactive-line cardinality identity then proves both positive run counts. Existing joint termination supplies bounded dimensions, normalization and the full residual predicates; the existing physical-side transport is reused directly. No positive-run assumption is placed on the input or its core.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraPartitionCore.residual_core_exists`
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraCanonicalJoint](MiuraCanonicalJoint.md)
- Dependency: [D5/S3/Combinatorics/Geometry/MiuraFiberCore](MiuraFiberCore.md)
