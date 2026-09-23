# Exact Feasibility Messages on Finite Forests

## Abstract

Finite forest constraints admit a simultaneous assignment exactly when every root residual domain survives.

**Theorem 1.1 (Root residuals characterize simultaneous avoidance).**

Lean statement: `D5/S3/Arith/Congruence/ExactForestMessages.exact_forest_message_feasibility`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ExactForestMessages.exact_forest_message_feasibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be any finite set of vertices. Each vertex has either one parent or no parent, and a natural-valued level strictly increases from each parent to its child. This ranking certifies a forest. Each vertex has a finite domain and a finite pure forbidden set in a common carrier Y. An arbitrary binary relation at each nonroot specifies the forbidden parent-child value pairs.

The theorem constructs finite residual domains A(v) and messages B(v). A parent value belongs to B(v) exactly when it conflicts with every value in A(v). The residual A(v) consists precisely of the values in the original domain that avoid the pure forbidden set and all messages sent by children of v. These equations use the original relations and allow empty residuals.

There exists one assignment of values to all vertices, respecting every domain and avoiding every pure and binary forbidden condition, if and only if A(v) is nonempty at every root. Messages at roots have no incoming edge and are unused in this equivalence; root failure is the emptiness of A(v).

Residual domains are constructed by recursion from children to parents. Every valid assignment lies in those residual domains, as a second bottom-up induction verifies. Conversely, choose a residual value at each root and recursively select a compatible residual value at each child. The child's surviving value is guaranteed by its parent's residual membership. Unique parents make these choices simultaneous across the forest, without any probabilistic independence hypothesis.

This is a direct formal construction of standard tree elimination. The result is uniform over all finite forests and finite domains, with arbitrary branching, arbitrarily long paths, and the empty forest included. The level is an increasing ranking certificate; it need not equal graph distance.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ExactForestMessages.exact_forest_message_feasibility`
