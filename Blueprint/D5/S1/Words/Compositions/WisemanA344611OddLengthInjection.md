# Wiseman A344611: odd-length partition injection

## Abstract

Nonnegative reverse-alternating partitions inject into odd-length partitions of the next weight.

**Definition 1.1 (Reverse-alternating sum).**

$$\forall (m: \mathbb{N}), \forall (p: \operatorname{Nat}.\operatorname{Partition}\left(m\right)), \operatorname{reverseAlternatingSum}\left(p\right) = \operatorname{List}.\operatorname{getLastD}\left(\operatorname{TrimmedAlternatingPartitions}.\operatorname{trimmedSums}\left(\operatorname{Multiset}.\operatorname{sort}\left(p.parts, ((a b: \mathbb{N}) \mapsto a \ge b)\right)\right), 0\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.reverseAlternatingSum` (`✓ std3`).

*Citation.* Gus Wiseman (2021). *OEIS A344611 — reverse-alternating sums of integer partitions*. URL: <https://oeis.org/A344611>.

*Commentary.*

OEIS A344611 revision 27, COMMENTS (electronic entry, no page number): “The reverse-alternating sum of a partition (y_1,...,y_k) is Sum_i (-1)^(k-i) y_i.” The parts are sorted decreasingly by Multiset.sort. The integer recurrence starts at zero and replaces z by a-z for each part a. Its last endpoint is this sum; List.getLastD gives zero for the empty list.

**Definition 1.2 (The A344611 count).**

$$\forall (n: \mathbb{N}), \operatorname{a344611}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Subtype}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(2 \cdot n\right)) \mapsto 0 \le \operatorname{reverseAlternatingSum}\left(p\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.a344611` (`✓ std3`).

*Citation.* Gus Wiseman (2021). *OEIS A344611 — reverse-alternating sums of integer partitions*. URL: <https://oeis.org/A344611>.

*Commentary.*

OEIS A344611 revision 27, NAME (electronic entry, no page number): “Number of integer partitions of 2*n with reverse-alternating sum >= 0.” Nat.card counts the finite subtype with that integer inequality.

**Definition 1.3 (The odd-length target count).**

$$\forall (n: \mathbb{N}), \operatorname{a160786}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left(\operatorname{Subtype}\left(((p: \operatorname{Nat}.\operatorname{Partition}\left(2 \cdot n+1\right)) \mapsto \operatorname{Odd}\left(p.parts.card\right))\right)\right)$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.a160786` (`✓ std3`).

*Citation.* Gus Wiseman (2021). *OEIS A344611 — reverse-alternating sums of integer partitions*. URL: <https://oeis.org/A344611>.

*Commentary.*

OEIS A160786 revision 25, FORMULA: “a(n) = A027193(2n+1).” OEIS A027193 revision 78, NAME: “Number of partitions of n into an odd number of parts.” These electronic entries have no page numbers. Odd refers to the number of parts, represented by p.parts.card, with no restriction on the sizes of individual parts.

**Definition 1.4 (The source comparison).**

$$claim \iff (\forall (n: \mathbb{N}), \operatorname{a344611}\left(n\right) \le \operatorname{a160786}\left(n\right))$$

*Formalization.* `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2021). *OEIS A344611 — reverse-alternating sums of integer partitions*. URL: <https://oeis.org/A344611>.

*Commentary.*

OEIS A344611 revision 27, FORMULA (electronic entry, no page number): “Conjecture: a(n) <= A160786(n). The difference is 0, 0, 0, 0, 1, 2, 4, 9, 16, 28, 48, 79, ...” The quantifier includes zero: OFFSET is “0,2”, and the source example includes ().

**Theorem 1.5 (The partition-count inequality).**

$$\forall (n: \mathbb{N}), \operatorname{a344611}\left(n\right) \le \operatorname{a160786}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.result` (`✓ std3`). ∎

*Resolves.* `Problems/wiseman-a344611` (proved) by `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wiseman-a344611","declaration_gid":"D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2021). *OEIS A344611 — reverse-alternating sums of integer partitions*. URL: <https://oeis.org/A344611>.

*Commentary.*

Increase the first part of an odd-length source by one, and append 1 to an even-length source. Both operations preserve decreasing order and positivity, increase the weight by one, and give odd length. A two-step integer endpoint bound forces the first two parts of a nonempty even-length source with nonnegative sum to agree. Thus the odd branch has a unique largest part and the even branch has a repeated largest part. The empty source maps to [1]. Inverting each branch gives an injection for every source weight m into odd-length partitions of m+1; cardinal comparison at m=2*n proves the inequality.

## References

- Truth anchor: `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.a160786`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.a344611`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.claim`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.result`
- Truth anchor: `D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.reverseAlternatingSum`
- Dependency: [D5/S1/Words/Compositions/TrimmedAlternatingPartitions](TrimmedAlternatingPartitions.md)
