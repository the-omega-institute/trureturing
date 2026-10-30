# A Counterexample to the Literal Adjacent Difference

## Abstract

The literal adjacent-column identity with the zero-based index n-4 fails at n=5: the actual cardinality difference is twenty and the absolute sequence value is six.

**Definition 1.1 (The zero-based auxiliary sequence).**

$$\forall m \in \mathrm{Nat},\; \operatorname{b}\left(m\right) = \frac{(-1)^{m} \cdot \operatorname{castQ}\left((m + 3)!\right)}{2 \cdot \operatorname{castQ}\left(m + 1\right)}$$

*Formalization.* `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.b` (`✓ std3`).

*Citation.* Wolfdieter Lang (2014). *OEIS A238474: a signed factorial quotient*. URL: <https://oeis.org/A238474>.

*Commentary.*

For every natural m, b(m) is (-1)^m times (m+3)! divided by 2(m+1), computed in the rationals. In the formulas, castQ denotes the natural-number embedding into the rationals. The factorial and m+1 are first computed in the natural numbers and then cast. The denominator is nonzero for every m >= 0. This is the formula of A238474 with offset zero: b(0)=3 and b(1)=-6. The exponent uses the rational number minus one, rather than natural truncated subtraction.

**Definition 1.2 (The literal adjacent-column conjecture).**

$$claim \Leftrightarrow \left(\forall n \in \mathrm{Nat},\; 4 \le n \Rightarrow \operatorname{castQ}\left(\operatorname{T}\left(n, n - 1\right)\right) - \operatorname{castQ}\left(\operatorname{T}\left(n, n - 2\right)\right) = \left|\operatorname{b}\left(n - 4\right)\right|\right)$$

*Formalization.* `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.claim` (`✓ std3`).

*Citation.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

The proposition claim asserts that for every natural n with 4 <= n, T(n,n-1)-T(n,n-2) equals the absolute value of b(n-4). Here T is the cardinality of all permutations of Fin n with no fixed point and no cycle factor of the forbidden length. Each cardinality is cast to the rationals before ordinary subtraction; the absolute value is rational. Every index subtraction is natural subtraction, and the hypothesis ensures that n-4 has its ordinary nonnegative meaning. The shift is exactly n-4, with no change of the zero offset of b and no upper bound on n.

**Theorem 1.3 (Five labels contradict the asserted equality).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378495-adjacent-difference` (refuted) by `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378495-adjacent-difference","declaration_gid":"D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

The proposition claim is false. At n=5, a derangement cannot contain a 4-cycle: the remaining label would be fixed. Thus excluded(5,4) is empty, whereas the cycle type (3,2) contributes exactly 5!/(2 times 3)=20 excluded permutations at length three. Applying the complementary-count identities to the same derangement set gives T(5,4)=T(5,3)+20 and hence the rational difference twenty. The source sequence has b(5-4)=b(1)=-6, whose absolute value is six. Since 20 differs from 6 and five satisfies the stated lower bound, this one exact counterexample negates the whole universal proposition. It does not assert a replacement formula or negate the separate terminal-column identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.b`
- Truth anchor: `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Derangements/AdjacentDifferenceRefutation.result`
- Dependency: [D5/S3/Combinatorics/Derangements/TerminalDifference](TerminalDifference.md)
