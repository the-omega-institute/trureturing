# Exact frozen-run length counts

## Abstract

Positive run lengths are actual indexed integer vectors.

**Definition 1.1 (Positive indexed lengths).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.PositiveLengths`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.PositiveLengths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural N and r, a length vector assigns a positive natural number to every index in Fin r, and the sum of all entries is N.

**Definition 1.2 (Remove the compulsory cell).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.removeOnesEquiv`

*Formalization.* `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.removeOnesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

If r is at most N, subtracting one from every run length gives a bijection with nonnegative indexed vectors of total N-r. The inverse adds one to every entry.

**Theorem 1.3 (The exact binomial cardinality).**

Lean statement: `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.positive_lengths_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.positive_lengths_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N and r with 1 at most r at most N, the actual positive indexed length vectors are counted by choose(N-1,r-1). The bijection removing one cell per run is composed with the pinned symmetric-power equivalence and its stars-and-bars cardinality. For frozen rows or columns, N is the available number of unoccupied positions and r is the number of maximal frozen runs.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.PositiveLengths`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.positive_lengths_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/MiuraRunCompositions.removeOnesEquiv`
