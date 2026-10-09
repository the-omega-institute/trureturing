# Union-closed counting exceeds the proposed threshold

## Abstract

Independent choices on a level of the Boolean lattice give too many labelled union-closed families for the proposed quasipolynomial threshold.

Bhattacharjee, Mandal and Bhattacharya ask in Question 9.2 of arXiv:2610.02833v1 whether a constant C makes the number of union-closed families of size N less than two to the power N minus one whenever N is at least n to the power C times the iterated base-two logarithm of n, for all sufficiently large n. Families are labelled subsets of the Boolean lattice.

**Definition 1.1 (The labelled count).**

$$\forall n \in \mathrm{Nat},\; \forall N \in \mathrm{Nat},\; \operatorname{U}\left(n, N\right) = \operatorname{card}\left(\{ F : \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right) | \operatorname{card}\left(F\right) = N \land \left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; A \in F \Rightarrow \left(\forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; B \in F \Rightarrow \operatorname{union}\left(A, B\right) \in F\right)\right) \}\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count finite families with exactly N members and closed under every binary union. No equivalence under permutations of the ground set is imposed.

**Definition 1.2 (The asserted eventual bound).**

$$claim \Leftrightarrow \left(\exists C \in \mathrm{Real},\; \exists cutoff \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; cutoff \le n \Rightarrow \left(\forall N \in \mathrm{Nat},\; \operatorname{castReal}\left(n\right)^{C \cdot \operatorname{logb}\left(2, \operatorname{logb}\left(2, \operatorname{castReal}\left(n\right)\right)\right)} \le \operatorname{castReal}\left(N\right) \Rightarrow \operatorname{U}\left(n, N\right) < 2^{N - 1}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real constant and the natural cutoff precede the universal quantifiers over dimension and family size. Natural subtraction occurs only in the integer exponent N minus one.

**Theorem 1.3 (A strict quarter-tail bound).**

$$\forall r \in \mathrm{Nat},\; 1 \le r \Rightarrow 4 \cdot \sum_{i \in \operatorname{range}\left(r\right)} \operatorname{choose}\left(6 \cdot r, i\right) < \operatorname{choose}\left(6 \cdot r, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.binomial_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write B for the r-th binomial coefficient in dimension six r and H for the sum of coefficients below it. The successive-coefficient identity gives (five r plus one) times each coefficient at most r times the next. Summing gives (four r plus one) H at most r times (B minus one), hence four H is less than B.

**Theorem 1.4 (Exponential growth of the chosen level).**

$$\forall r \in \mathrm{Nat},\; 6^{r} \le \operatorname{choose}\left(6 \cdot r, r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.binomial_level_growth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vandermonde's identity gives at least six choices for each additional block of six points. Induction yields B at least six to the power r.

**Theorem 1.5 (Independent four-way selections).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall q \in \mathrm{Nat},\; 4 \cdot q \le \operatorname{choose}\left(n, k\right) \Rightarrow \left(\exists f \in \left(\operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(4\right)\right) \to \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right),\; \operatorname{Injective}\left(f\right) \land \left(\forall x \in \operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(4\right),\; \operatorname{card}\left(\operatorname{f}\left(x\right)\right) = \operatorname{card}\left(\{ A : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) | k < \operatorname{card}\left(A\right) \}\right) + q \land \left(\forall A \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; A \in \operatorname{f}\left(x\right) \Rightarrow \left(\forall B \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; B \in \operatorname{f}\left(x\right) \Rightarrow \operatorname{union}\left(A, B\right) \in \operatorname{f}\left(x\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.level_selection_injection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Embed q disjoint quadruples in the level of k-element subsets. For each function from q indices to four choices, include its q selected sets and every set of cardinality greater than k. This family is upward-closed: any strict superset of a selected set belongs to the upper tail. Its size is the upper-tail size plus q, and distinct functions give distinct families.

**Theorem 1.6 (The resulting counting lower bound).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall q \in \mathrm{Nat},\; 4 \cdot q \le \operatorname{choose}\left(n, k\right) \Rightarrow 4^{q} \le \operatorname{U}\left(n, \operatorname{card}\left(\{ A : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right) | k < \operatorname{card}\left(A\right) \}\right) + q\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.level_selection_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The injection supplies at least four to the power q distinct union-closed families at the specified size.

**Theorem 1.7 (Complementation identifies the tails).**

$$\forall r \in \mathrm{Nat},\; \operatorname{card}\left(\{ A : \operatorname{Finset}\left(\operatorname{Fin}\left(6 \cdot r\right)\right) | 5 \cdot r < \operatorname{card}\left(A\right) \}\right) = \sum_{i \in \operatorname{range}\left(r\right)} \operatorname{choose}\left(6 \cdot r, i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.upper_tail_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complementation bijects subsets of size greater than five r with subsets of size less than r. Partitioning the latter by cardinality gives H.

**Theorem 1.8 (Exponential-sized counterexamples).**

$$\forall r \in \mathrm{Nat},\; 4 \le r \Rightarrow \left(2^{r} \le \sum_{i \in \operatorname{range}\left(r\right)} \operatorname{choose}\left(6 \cdot r, i\right) + \operatorname{NatDiv}\left(\operatorname{choose}\left(6 \cdot r, r\right), 4\right) \land 2^{\sum_{i \in \operatorname{range}\left(r\right)} \operatorname{choose}\left(6 \cdot r, i\right) + \operatorname{NatDiv}\left(\operatorname{choose}\left(6 \cdot r, r\right), 4\right)} \le \operatorname{U}\left(6 \cdot r, \sum_{i \in \operatorname{range}\left(r\right)} \operatorname{choose}\left(6 \cdot r, i\right) + \operatorname{NatDiv}\left(\operatorname{choose}\left(6 \cdot r, r\right), 4\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.counting_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Set q to the integer quotient B divided by four and N to H plus q. The tail bound gives H at most q. Thus two to the power N is at most four to the power q and hence at most the labelled count. For r at least four, the level-growth estimate also gives N at least two to the power r.

**Theorem 1.9 (The threshold is eventually met).**

$$\forall C \in \mathrm{Real},\; \exists cutoff \in \mathrm{Nat},\; \forall r \in \mathrm{Nat},\; cutoff \le r \Rightarrow \operatorname{castReal}\left(6 \cdot r\right)^{C \cdot \operatorname{logb}\left(2, \operatorname{logb}\left(2, \operatorname{castReal}\left(6 \cdot r\right)\right)\right)} \le 2^{r}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.eventual_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real C, the square of the base-two logarithm divided by dimension tends to zero. The iterated logarithm is bounded by the first logarithm divided by log two. Consequently the exponent after conversion to base two is eventually at most r, even for an arbitrary fixed C.

**Theorem 1.10 (Question 9.2 has a negative answer).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/bhattacharjee-mandal-bhattacharya-2026-union-closed-count-refutation` (refuted) by `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhattacharjee-mandal-bhattacharya-2026-union-closed-count-refutation","declaration_gid":"D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Choose r large enough to exceed the dimension cutoff and meet the threshold. The constructed size N satisfies the hypothesis while its count is at least two to the power N, contradicting the asserted strict upper bound. This settles the counting question; it does not refute the underlying Erdős–Ulam union-closed extremal problem or Proposition 5.4's conditional implication.

## References

- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.U`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.binomial_level_growth`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.binomial_tail_bound`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.counting_counterexample`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.eventual_threshold`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.level_selection_count`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.level_selection_injection`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/ErdosUlam/UnionClosedCountRefutation.upper_tail_card`
