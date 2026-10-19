# Exact weak-four metric dimension of complete graph direct squares

## Abstract

Exact weak-four metric dimension of complete graph direct squares

Farhan, Kuziak and Yero, arXiv:2605.22307v1, Section 3 paragraph S3.p17.1 and Section 6 first bullet ask for this value for every n at least four. Adjacency changes both coordinates. Weak resolution quantifies over distinct pairs, as explicitly stated in Proposition 2.2. The finite feasible family has an attained minimum.

**Theorem 1.1 (Universal landmark lower bound).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.lower_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least four, every actual weak-four landmark set has at least target n elements. Sets at or above 3n minus 2 already exceed the target. Smaller sets have incidence minimum degree two, so the linear lower bound gives the ceiling term. At order five, the eleven-element equality possibility is excluded.

**Theorem 1.2 (Nonempty feasible family and attainment).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.minimum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least four there exists a weak-four landmark set with cardinality target n, and its cardinality is no larger than that of every weak-four landmark set.

**Definition 1.3 (The exact original formula).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n at least four, the actual weak-four dimension is 2n plus the ceiling of 2n over eleven, plus one exactly when n equals five. Natural division of 2n plus 10 by eleven represents the ceiling.

**Theorem 1.4 (Exact weak-four dimension).**

Lean statement: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result` (`✓ std3`). ∎

*Resolves.* `Problems/farhan-kuziak-yero-2026-direct-square-weak-four` (proved) by `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"farhan-kuziak-yero-2026-direct-square-weak-four","declaration_gid":"D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

The formula holds at every n at least four. The construction gives nonemptiness and an attained feasible cardinality, while the universal lower bound applies to every feasible cardinality. Therefore the natural infimum is the true least cardinality. In particular the value at order nine is twenty; the upper bound twenty-one from source Theorem 3.3 is not always sharp.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.minimum`
- Truth anchor: `D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exact.result`
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Construction](Construction.md)
- Dependency: [D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Exception](Exception.md)
