# Coordinate exchange on the actual square graph

## Abstract

Transposition of the square grid

**Definition 1.1 (Square-strip graph isomorphism).**

Lean statement: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport/SquareTranspose.squareTranspose`

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport/SquareTranspose.squareTranspose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any positive height h and width k, coordinate exchange sends (i,j) in the h by k square grid to (j,i) in the k by h grid. A horizontal bond with column endpoints j and j+1 becomes a vertical bond with row endpoints j and j+1. A vertical bond becomes a horizontal bond by the same rule. The reverse orientations are exchanged as well. Swapping a second time recovers the original coordinates, giving a graph isomorphism even when one dimension is one.

## Normalized square counts and A233129

The literal strip equivalence flattens each rectangle using its own row-major order and identifies its assignments with the corresponding normalized graph words. The square isomorphism, conjugated by the two row-major enumerations, transports proper colourings for each palette, with inverse transport along the inverse isomorphism. The total identity on a nonempty graph with N vertices expresses 48 times the normalized count as 2^N times (P(3)+3P(2)+15P(1)), where P(q) counts proper q-colourings. Here both vertex counts equal hk, so cancellation gives equality of the two normalized cardinalities. Each scan uses its own first occurrences.

The positive square entries of Hardin's A233129 therefore satisfy U(h,k)=U(k,h). The 1×1 grid has one admissible value for its single cell. A path on n≥2 cells has (4^(n−2)+2^(n−2))/2 assignments, equivalently 2^(n−3)(1+2^(n−2)), with a reciprocal power at n=2. Both orientations inherit the Deutsch recurrence with coefficients 6 and −8 from n≥4. The path count is A007582 at index n−2, including the term at index zero, by the marked-partition correspondence attributed to Britnell and Wildon.

For a growing positive dimension n, the width-two square word has the same literal predicate as A233123 and the width-three square word has the same literal predicate as A233124. The existing square recurrences start at n=3 and n=4 respectively. Their coefficients are (16,−48) and (48,−448,1024), with positive initial values (1,8) and (3,80,2688).

The width-two generating function is x(1−8x)/((1−4x)(1−12x)) and the width-three generating function is x(3−64x+192x²)/((1−8x)(1−40x+128x²)). Both start at x¹, with zero constant coefficient. For n≥1 the corresponding counts are (12^n+3·4^n)/24 and 8^(n−1)+((t−3)(20−4t)^n+(t+3)(20+4t)^n)/(32t), where t=√17. The formulas in A233123 and A233124 were conjectured by Colin Barker. The literal cardinality identities apply these formulas to both orientations.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport/SquareTranspose.squareTranspose`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinThinGraphTransport](../HardinThinGraphTransport.md)
