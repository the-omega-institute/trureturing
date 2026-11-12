# Nine-element restriction

## Abstract

Restriction of marked-prefix and unmarked-pair counts to nine-element subsets.

**Theorem 1.1 (Counting extensions of a selected prefix and pair).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction_count`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural block sizes m and n and rank k between three and five, sum over j from zero through nine the product choose(m,j) choose(n,9-j) choose(j,k-1) choose(9-j,2). This equals choose(m,k-1) choose(n,2) choose(m+n-(k+1),9-(k+1)). All subtractions here are natural subtractions, and binomial coefficients vanish outside their natural support.

Only k-1 through seven can contribute. Shifting by k-1 and applying the composed-choice identity in each block leaves Vandermonde convolution on the remaining elements. If either block cannot supply its selected elements, both sides vanish. This counts extensions in arbitrary populations, rather than only a population of size nine.

**Theorem 1.2 (The exact restriction average).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N at least nine, m at most N and k from three through five, define H(N,m,k) as choose(m,k-1) choose(N-m,2) divided by choose(N,k+1) choose(k+1,2), with rational division. Then H(N,m,k) equals the sum over zero through nine of w(j) H(9,j,k), where w(j) is choose(m,j) choose(N-m,9-j) divided by choose(N,9).

Every denominator is positive: k+1 lies between four and six and is at most nine and N. The integer extension count and the composed-choice identity cancel the number of extensions of a selected (k+1)-subset to a nine-subset.

**Theorem 1.3 (Uniform small-rank bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every N at least nine and m at most N, the rational quantity H(N,m,k) is at most 5/63 for k=3, at most 1/21 for k=4, and at most 1/28 for k=5. The theorem states these three values as one rank-indexed bound.

The weights are nonnegative, and Vandermonde convolution shows that they sum to one. For j from zero through nine the numerators choose(j,k-1) choose(9-j,2) have respective maxima 60, 60 and 45. Their denominators are 756, 1260 and 1260. Applying these finite bounds inside the exact restriction average proves the stated bounds for all N. Three such nonnegative contributions are consequently bounded by 5/21, 1/7 and 3/28, respectively.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.nine_restriction_count`
