# Fourth-moment compression

## Abstract

Fourth-moment compression and separately polynomial averages.

**Definition 1.1 (Monomial coordinates).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.Monomial`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.Monomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index set consists of unordered multisets of four optional coordinate indices. Its cardinality is choose(k+4,4), including the constant monomial and every total degree up to four.

**Definition 1.2 (Padded monomial evaluation).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.monomial`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.monomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A multiset of four optional coordinates represents a monomial of degree at most four. A missing coordinate contributes one. Every lower degree is included by padding with missing coordinates.

**Definition 1.3 (A fixed node count).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.nodeCount`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.nodeCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For k variables the fourth-degree feature space has choose(k+4,4) coordinates. One additional node suffices for every convex combination in this feature space.

**Definition 1.4 (Fourth-degree polynomials).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.quartic`

*Formalization.* `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.quartic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coefficient vectors on the padded monomial indices represent real polynomials of total degree at most four.

**Theorem 1.5 (Fixed-size moment compression).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.exists_moment_compression`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.exists_moment_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty finite family of real k-dimensional points there are exactly choose(k+4,4)+1 nodes taken from that family and nonnegative weights of sum one preserving every monomial average through total degree four. Caratheodory reduction supplies the nodes, and zero weights pad a shorter representation. The nodes therefore stay in every set containing the original family.

**Theorem 1.6 (Polynomial averages).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.quartic_average_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.quartic_average_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of the monomial averages implies equality of the average of every polynomial represented by a coefficient vector on these indices. Finite sums commute and each monomial equality applies separately.

**Theorem 1.7 (Separately fourth-degree double averages).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.product_average_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.product_average_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Moment equality preserves the double average of every finite sum of products f(x)g(y), where each factor is a polynomial of degree at most four. This includes total degree eight across the two arguments. The double average factors into the product of the two single averages before the moment identities are applied.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.Monomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.exists_moment_compression`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.monomial`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.nodeCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.product_average_eq`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.quartic`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/MomentCompression.quartic_average_eq`
