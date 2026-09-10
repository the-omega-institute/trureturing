# A359482 is not a permutation

## Abstract

The greedy decimal sequence A359482 omits every single-digit successor and therefore omits 2.

All variables are natural numbers. D(x) is the decimal digit list with the most significant digit first, no leading zeros, and D(0)=[0]. Legal(x,y) means that D(x+y) is a contiguous sublist of D(x) followed by D(y). For example, 11 occurs in 110, 109 in 1099, and 988 in 99889.

The initial state is (1,{1}). Given the current term x and finite used set U, next(x,U) is the natural infimum of positive y outside U satisfying Legal(x,y). The next state is (next(x,U), U union {next(x,U)}). The function seq(n) reads the current term after n-1 steps; seq(1)=1, and seq(0)=1 by convention.

**Theorem 1.1 (No positive single-digit successor).**

$$\forall x \in \mathbb{N}, \forall d \in \mathbb{N}, 0 < x \implies (0 < d \land d < 10) \implies \neg\operatorname{Legal}\left(x, d\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation.no_small_successor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Angelini, Hans Havermann, and M. F. Hasler (2023). *OEIS A359482 and the single-digit conjecture*. URL: <https://oeis.org/A359482>.

*Commentary.*

The sum has at least as many digits as x. Reverse the occurrence and split at its first position: an occurrence wholly in the old digits forces x+d=x. Otherwise it is a prefix of d followed by those digits, with at most one digit left over. No leftover forces x+d=d+10x. A leftover a gives old digits r followed by a and sum digits d followed by r. Evaluation forces a times 10^length(r)=9 times value(r). Modulo nine gives a=0 or a=9. The first forces x=0; the second forces value(r)=10^length(r), contradicting the strict digit-value bound. The empty list r is included.

**Theorem 1.2 (The original least-unused rule).**

$$\forall k \in \mathbb{N}, \operatorname{seq}\left(k + 2\right) = \operatorname{sInf}\left(\operatorname{candidates}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation.sequence_greedy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Angelini, Hans Havermann, and M. F. Hasler (2023). *OEIS A359482 and the single-digit conjecture*. URL: <https://oeis.org/A359482>.

*Commentary.*

Here candidates(k) consists exactly of positive y such that y differs from seq(i+1) for every 0<=i<=k and Legal(seq(k+1),y) holds. Induction identifies the stored used set with the image of the preceding indices. Thus this equality states the original lexicographic greedy rule.

**Theorem 1.3 (Positive terms at every index).**

$$\forall n \in \mathbb{N}, 0 < \operatorname{seq}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation.sequence_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Angelini, Hans Havermann, and M. F. Hasler (2023). *OEIS A359482 and the single-digit conjecture*. URL: <https://oeis.org/A359482>.

*Commentary.*

Put P=10^length(D(x)), R(0)=x, R(k+1)=x+P R(k). The digits of R(k) repeat D(x), and P R(k) is a legal successor: the sum occurs before the trailing zero block in the concatenation. These successors exceed k, so one lies outside every finite used set. The defining infimum therefore belongs to the positive candidate set. Induction proves positivity of all terms.

**Theorem 1.4 (Adjacent terms satisfy the substring rule).**

$$\forall n \in \mathbb{N}, 1 \le n \implies \operatorname{Legal}\left(\operatorname{seq}\left(n\right), \operatorname{seq}\left(n + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation.sequence_legal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Angelini, Hans Havermann, and M. F. Hasler (2023). *OEIS A359482 and the single-digit conjecture*. URL: <https://oeis.org/A359482>.

*Commentary.*

The same nonempty candidate set ensures that each chosen minimum satisfies the decimal substring condition.

**Theorem 1.5 (Every term after the first is at least ten).**

$$\forall n \in \mathbb{N}, 2 \le n \implies 10 \le \operatorname{seq}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation.sequence_tail_ge_ten` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Angelini, Hans Havermann, and M. F. Hasler (2023). *OEIS A359482 and the single-digit conjecture*. URL: <https://oeis.org/A359482>.

*Commentary.*

Positivity and the adjacent-pair rule allow the no-single-digit theorem to be applied at every index from two onwards.

**Theorem 1.6 (The positive integer two is missing).**

$$\neg(\forall m \in \mathbb{N}, 0 < m \implies \exists n \in \mathbb{N}, 1 \le n \land \operatorname{seq}\left(n\right) = m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation.not_positive_permutation` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a359482-positive-permutation` (refuted) by `D5/S3/Arith/SumInConcatenation.not_positive_permutation`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a359482-positive-permutation","declaration_gid":"D5/S3/Arith/SumInConcatenation.not_positive_permutation","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Eric Angelini, Hans Havermann, and M. F. Hasler (2023). *OEIS A359482 and the single-digit conjecture*. URL: <https://oeis.org/A359482>.

*Commentary.*

The first term is 1. Every later term is at least 10. Hence 2 has no positive index, so the sequence is not surjective onto the positive integers and cannot be a permutation. This answers the permutation question in OEIS A359482; it does not address the stronger multiples-of-ten conjecture.

## References

- Truth anchor: `D5/S3/Arith/SumInConcatenation.no_small_successor`
- Truth anchor: `D5/S3/Arith/SumInConcatenation.not_positive_permutation`
- Truth anchor: `D5/S3/Arith/SumInConcatenation.sequence_greedy`
- Truth anchor: `D5/S3/Arith/SumInConcatenation.sequence_legal`
- Truth anchor: `D5/S3/Arith/SumInConcatenation.sequence_pos`
- Truth anchor: `D5/S3/Arith/SumInConcatenation.sequence_tail_ge_ten`
