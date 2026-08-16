# Orthogonal Projections onto Complementary Subspaces

## Abstract

Complementary orthogonal projections satisfy the six canonical operator identities.

**Theorem 1.1 (Closed-subspace projections obey the complement identities).**

$$\forall k, E: \operatorname{Type},\ [\operatorname{RCLike}(k)],\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}_{k}(E)],\ [\operatorname{CompleteSpace}(E)],\ M: \operatorname{ClosedSubmodule}_{k}(E),\ P_{M^{\perp}} = I - P_{M} \land P_{M} \circ P_{M} = P_{M} \land P_{M^{\perp}} \circ P_{M^{\perp}} = P_{M^{\perp}} \land P_{M} \circ P_{M^{\perp}} = 0 \land P_{M^{\perp}} \circ P_{M} = 0 \land P_{M} + P_{M^{\perp}} = I.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/OrthogonalProjectionComplement.orthogonal_complement_projection_identities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let M be a closed subspace of a complete real or complex inner-product space, and let P with subscript M denote its orthogonal projection. The projection onto the orthogonal complement is the identity minus P with subscript M.

Both projections are idempotent. Their compositions vanish in both orders, and their sum is the identity operator. These are all six equalities in the named statement, retained as one conjunction.

Loogle and the pinned Mathlib tree supplied the exact complementary, idempotence, orthogonality, and sum declarations used by the Lean proof. The LeanSearch endpoint attempted for corroboration returned HTTP 404.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/OrthogonalProjectionComplement.orthogonal_complement_projection_identities`
