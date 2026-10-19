# Equality-size constructions at every order

## Abstract

Equality-size constructions at every order

The finite base sets are explicit coordinate lists. Their degree, path and rectangle properties are checked by kernel reduction. An induction adjoining an eleven-by-eleven block proves the unrestricted construction; no finite range is extrapolated.

**Definition 1.1 (Exact cardinality expression).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.target`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.target` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, target n is 2n plus natural division of 2n plus 10 by eleven, with one extra landmark exactly at n equal to five. The division term is the ceiling of 2n over eleven.

**Theorem 1.2 (Every incidence size).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.all_design`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.all_design` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least four there is a Good incidence set with exactly target n edges. Explicit base designs cover orders four through sixteen. For every larger order remove eleven, use the smaller design, adjoin the twenty-four-edge order-eleven block, and relabel both parts. The natural ceiling increases by exactly two.

**Theorem 1.3 (Actual equality-size landmark sets).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.construction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.construction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least four a finite set of actual direct-product vertices is weak four-resolving and has cardinality exactly target n.

**Theorem 1.4 (Strict low-degree threshold).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.target_lt_three`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.target_lt_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least four the target is strictly less than 3n minus 2. This makes the minimum-degree-two reduction available whenever a set could beat the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.all_design`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.construction`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.target`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction.target_lt_three`
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design](Design.md)
