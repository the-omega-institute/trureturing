# Cardinality-Sum-Avoiding Subsets

## Abstract

The original subset count has the conjectured generating function.

For every natural n, the interval [1,n] is empty at n=0. A subset S is admissible when no distinct x,y in S satisfy x+y=|S|. The test does not prohibit an element x with 2x=|S|. All counts are natural numbers. X is the formal indeterminate; the generating-function identity lies in Q[[X]], with natural counts cast to Q. No analytic convergence or recurrence-defined substitute is assumed.

**Definition 1.1 (The original admissible family).**

$$\operatorname{admissibleFamily}\left(n\right) = \{S \subseteq \operatorname{Icc}\left(1, n\right) \mid \forall x,y \in S, (x \neq y) \implies (x + y \neq \operatorname{card}\left(S\right))\}$$

*Formalization.* `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.admissibleFamily` (`✓ std3`).

*Citation.* Gus Wiseman; Chai Wah Wu (2023). *OEIS A367400: cardinality-sum-avoiding subsets*. URL: <https://oeis.org/A367400>.

*Commentary.*

The finite family is the powerset of the natural interval [1,n], filtered by the displayed predicate. This is exactly the OEIS NAME convention, including the empty subset and permission for equal summands.

**Definition 1.2 (The original sequence).**

$$\operatorname{a}\left(n\right) = \operatorname{card}\left(\operatorname{admissibleFamily}\left(n\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.a` (`✓ std3`).

*Citation.* Gus Wiseman; Chai Wah Wu (2023). *OEIS A367400: cardinality-sum-avoiding subsets*. URL: <https://oeis.org/A367400>.

*Commentary.*

The sequence is the cardinality of that actual finite family. Its zero coefficient is one because the empty subset is its sole member at n=0.

**Theorem 1.3 (The formal generating-function identity).**

$$(1 - 2 \cdot X + X^{2} - 2 \cdot X^{3} + X^{4}) \cdot \sum_{n = 0}^{\infty} \operatorname{a}\left(n\right) X^{n} = 1 + X^{2} - X^{3}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a367400-cardinality-sum-avoiding-subsets` (proved) by `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a367400-cardinality-sum-avoiding-subsets","declaration_gid":"D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2023). *OEIS A367400: cardinality-sum-avoiding subsets*. URL: <https://oeis.org/A367400>.

*Commentary.*

For each positive cardinality k, the proof constructs an invertible encoding by disjoint pairs {i,k-i}, an optional even midpoint, and the unrestricted tail [k,n]. It derives the count polynomial, uses Mathlib's binomial-series and homogenization identities, and sums the two parity families coefficientwise. Every coefficient involves only finitely many cardinalities. The empty subset is handled separately. All helper proofs and equivalences are local to result.

## References

- Truth anchor: `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.a`
- Truth anchor: `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.admissibleFamily`
- Truth anchor: `D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.result`
