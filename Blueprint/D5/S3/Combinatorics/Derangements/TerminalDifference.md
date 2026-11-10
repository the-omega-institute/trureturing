# The Terminal Difference of the Derangement Triangle

## Abstract

For every natural n at least five, the difference T(n,n-2)-T(n,n) for derangements avoiding a cycle length is (n-3)!(n-4)(n-1)/2.

**Definition 1.1 (Derangements on n labels).**

$$\forall n \in \mathrm{Nat},\; \operatorname{D}\left(n\right) = \{p \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right) \mid \forall x \in \operatorname{Fin}\left(n\right),\; p\left(x\right) \ne x\}$$

*Formalization.* `D5/S3/Combinatorics/Derangements/TerminalDifference.D` (`✓ std3`).

*Citation.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n, D(n) is the finite set of all permutations p of Fin n such that p(x) differs from x for every label x. The labels are the integers from zero to n-1. Relabelling them from one to n gives the symmetric group in the source definition. At n=0 the empty permutation satisfies the condition vacuously; no positivity assumption is built into D.

**Definition 1.2 (The triangle entry).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{T}\left(n, k\right) = \operatorname{card}\left(\{p \in \operatorname{D}\left(n\right) \mid \forall c \in \operatorname{cycleFactorsFinset}\left(p\right),\; \operatorname{card}\left(\operatorname{support}\left(c\right)\right) \ne k\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Derangements/TerminalDifference.T` (`✓ std3`).

*Citation.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For natural n and k, T(n,k) is the cardinality of the subset of D(n) in which every cycle factor has support cardinality different from k. On the source-agreeing columns 2 <= k <= n this counts exactly the derangements with no k-cycle. The source entry separately sets its k=1 column to zero, whereas this total formal extension has T(n,1)=card(D(n)) because derangements have no fixed points. The definition is total also at zero and outside the triangular range; the two registered identities use only source-agreeing columns: n-2 and n are at least three for n >= 5, while n-1 and n-2 are at least two for n >= 4.

**Definition 1.3 (Derangements containing a forbidden cycle).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{excluded}\left(n, k\right) = \{p \in \operatorname{D}\left(n\right) \mid k \in \operatorname{cycleType}\left(p\right)\}$$

*Formalization.* `D5/S3/Combinatorics/Derangements/TerminalDifference.excluded` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For natural n and k, excluded(n,k) is the subset of D(n) whose multiset of nontrivial cycle lengths contains k. Membership records the existence of at least one such cycle, rather than counting occurrences or selecting a distinguished cycle. Its cardinality therefore counts excluded permutations once each.

**Theorem 1.4 (Cycle factors and cycle type).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \forall p \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \left(\forall c \in \operatorname{cycleFactorsFinset}\left(p\right),\; \operatorname{card}\left(\operatorname{support}\left(c\right)\right) \ne k\right) \Leftrightarrow \left(\neg k \in \operatorname{cycleType}\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.noCycle_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n and k and every permutation p of Fin n, all cycle factors of p have support cardinality different from k if and only if k is absent from p's cycle type. The cycle type is the multiset of support sizes of the nontrivial cycle factors. No derangement or positivity assumption is needed for this equivalence, including k=0 and k=1.

**Theorem 1.5 (The excluded and retained permutations partition D).**

$$\forall n \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{T}\left(n, k\right) + \operatorname{card}\left(\operatorname{excluded}\left(n, k\right)\right) = \operatorname{card}\left(\operatorname{D}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.T_add_excluded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n and k, T(n,k) plus the cardinality of excluded(n,k) equals the cardinality of D(n). The two filters are complementary predicates on the same finite set; a permutation with several k-cycles still belongs to only one part. This is an equality of natural cardinalities and involves no subtraction.

**Theorem 1.6 (Recognizing derangements from cycle type).**

$$\forall n \in \mathrm{Nat},\; \forall p \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; p \in \operatorname{derangements}\left(\operatorname{Fin}\left(n\right)\right) \Leftrightarrow \operatorname{sum}\left(\operatorname{cycleType}\left(p\right)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.noFixed_iff_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n and permutation p of Fin n, p has no fixed point if and only if the sum of its nontrivial cycle lengths is n. That sum is the cardinality of the support of p; on an n-label set it equals n precisely when every label is moved. The equivalence includes the empty permutation at n=0.

**Theorem 1.7 (A multiset of total size two).**

$$\forall s \in \operatorname{Multiset}\left(\mathrm{Nat}\right),\; \operatorname{sum}\left(s\right) = 2 \Rightarrow \left(\left(\forall a \in s,\; 2 \le a\right) \Rightarrow s = \operatorname{multiset}\left(2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.sum_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For any multiset s of natural numbers, if its sum is two and every member is at least two, then s is the singleton multiset containing two. A nonempty remainder would contribute at least two more to the sum. The lower bound on every member rules out zero entries and entries of size one.

**Theorem 1.8 (The terminal cycle type).**

$$\forall n \in \mathrm{Nat},\; \forall p \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \left(p \in \operatorname{derangements}\left(\operatorname{Fin}\left(n\right)\right) \land n \in \operatorname{cycleType}\left(p\right)\right) \Leftrightarrow \operatorname{cycleType}\left(p\right) = \operatorname{multiset}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.terminal_cycleType` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n and permutation p of Fin n, being a derangement and having n in the cycle type is equivalent to having cycle type exactly the singleton multiset containing n. An n-cycle exhausts the labels. There is no lower-bound hypothesis: when n is zero or one, both sides are false because cycle type contains only lengths at least two.

**Theorem 1.9 (The cycle type containing n-2).**

$$\forall n \in \mathrm{Nat},\; 5 \le n \Rightarrow \left(\forall p \in \operatorname{Perm}\left(\operatorname{Fin}\left(n\right)\right),\; \left(p \in \operatorname{derangements}\left(\operatorname{Fin}\left(n\right)\right) \land n - 2 \in \operatorname{cycleType}\left(p\right)\right) \Leftrightarrow \operatorname{cycleType}\left(p\right) = \operatorname{multiset}\left(n - 2, 2\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.penultimate_cycleType` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n at least five and permutation p of Fin n, being a derangement with n-2 in its cycle type is equivalent to having cycle type exactly the two-member multiset containing n-2 and two. Removing the n-2 part leaves total size two, and all remaining parts are at least two. The bound makes n-2 at least three, so these two lengths are distinct. All index subtractions are natural subtraction.

**Theorem 1.10 (Counting the excluded n-cycles).**

$$\forall n \in \mathrm{Nat},\; 5 \le n \Rightarrow \operatorname{card}\left(\operatorname{excluded}\left(n, n\right)\right) = (n - 1)!$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.excluded_terminal_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n at least five, the cardinality of excluded(n,n) is (n-1)!. These are exactly the permutations with cycle type consisting of n alone. The singleton cycle-type counting formula gives (n-1)! times choose(n,n), and the binomial factor is one. Factorial and n-1 are natural-number operations.

**Theorem 1.11 (Counting the excluded two-cycle types).**

$$\forall n \in \mathrm{Nat},\; 5 \le n \Rightarrow \operatorname{card}\left(\operatorname{excluded}\left(n, n - 2\right)\right) \cdot 2 \cdot \left(n - 2\right) = (n)!$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.excluded_penultimate_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n at least five, the cardinality of excluded(n,n-2), multiplied by 2(n-2), is n!. The contributing cycle type consists of two distinct lengths n-2 and two, covers all labels and has multiplicity one for each length. Its cycle-count denominator is therefore 2(n-2). This is a division-free equality in the natural numbers; n-2 is positive under the stated bound.

**Theorem 1.12 (The terminal-column identity).**

$$\forall n \in \mathrm{Nat},\; 5 \le n \Rightarrow \operatorname{castQ}\left(\operatorname{T}\left(n, n - 2\right)\right) - \operatorname{castQ}\left(\operatorname{T}\left(n, n\right)\right) = \frac{\operatorname{castQ}\left((n - 3)!\right) \cdot \operatorname{castQ}\left(n - 4\right) \cdot \operatorname{castQ}\left(n - 1\right)}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Derangements/TerminalDifference.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a378495-terminal-difference` (proved) by `D5/S3/Combinatorics/Derangements/TerminalDifference.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a378495-terminal-difference","declaration_gid":"D5/S3/Combinatorics/Derangements/TerminalDifference.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Kagey (2024). *OEIS A378495: derangements with no k-cycles*. URL: <https://oeis.org/A378495>.

*Commentary.*

For every natural n with 5 <= n, cast both triangle cardinalities to the rationals before subtracting. In the formulas, castQ denotes the natural-number embedding into the rationals. Their difference T(n,n-2)-T(n,n) equals (n-3)!(n-4)(n-1)/2, with the factorial and all index subtractions evaluated in the natural numbers and then cast to the rationals. The only hypothesis is 5 <= n, with no upper bound. The partition identity turns the difference into (n-1)! minus the number of permutations of cycle type (n-2,2). Substituting their count n!/(2(n-2)) and expanding factorials yields the displayed expression. Cancellation is valid because n-2 is nonzero; the bound also justifies replacing casts of n-4 and n-1 by rational subtraction. The final division by two is rational division.

## References

- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.D`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.T`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.T_add_excluded`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.excluded`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.excluded_penultimate_mul`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.excluded_terminal_card`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.noCycle_iff`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.noFixed_iff_sum`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.penultimate_cycleType`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.result`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.sum_two`
- Truth anchor: `D5/S3/Combinatorics/Derangements/TerminalDifference.terminal_cycleType`
