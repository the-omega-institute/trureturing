# Two-digit multiples of ten in A359482

## Abstract

In the original greedy decimal sequence A359482, 10 occurs at index 2 and none of 20,30,...,90 occurs at any index.

All variables are natural numbers. The decimal digit list D, substring predicate Legal, least positive unused legal successor next, finite used-set state, and sequence seq are those of SumInConcatenation. Indexing begins at 1, with seq(0)=seq(1)=1. The legality condition uses the sum in the decimal concatenation, in the original order.

Hasler's independent full proof establishes the published conjecture. The earlier Ma-Zhang Lean contribution proves the single-digit part and supplies the sequence definitions used here. The three-position argument below retains the exceptional predecessor x=m before applying the sequence's tail bound.

**Theorem 1.1 (Exact legal predecessors of a two-digit multiple of ten).**

$$\forall x \in \mathbb{N}, \forall m \in \mathbb{N}, 0 < x \implies (1 \le m \land m < 10) \implies (\operatorname{Legal}\left(x, 10 \cdot m\right) \iff x = m)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation/DecimalMultiples.legal_multiple_ten_iff` (`✓ std3`). ∎

*Citation.* M. F. Hasler (2026). *A359482, Proof by MFH*. URL: <https://oeis.org/w/index.php?title=A359482&oldid=1675118>.

*Commentary.*

Reverse the decimal occurrence. The concatenation begins with 0,m and then the digits of x. The sum has at least as many digits as x, so there are three possible starting positions. Writing q for ten to the number of digits of the sum, the first position gives 99x=qR. Coprimality of q with 99 and 0<x<q exclude it. The second gives 9(x-m)=qR, with m<=x; coprimality with 9 and x-m<q force x=m. A position entirely inside x forces the sum to equal x, impossible for m>0. Conversely x=m satisfies the substring rule for all nine admissible digits. This is the successor-multiple passage in Proof by MFH.

**Theorem 1.2 (The terms 20 through 90 are absent at every index).**

$$\forall n \in \mathbb{N}, \forall m \in \mathbb{N}, (2 \le m \land m < 10) \implies \operatorname{seq}\left(n\right) \neq 10 \cdot m$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation/DecimalMultiples.sequence_ne_multiple_ten` (`✓ std3`). ∎

*Citation.* M. F. Hasler (2026). *A359482, Proof by MFH*. URL: <https://oeis.org/w/index.php?title=A359482&oldid=1675118>.

*Commentary.*

Indices 0 and 1 have value 1. At every later index, legality forces the preceding term to be m. The preceding term is either the initial 1 or is at least 10; neither lies between 2 and 9. The exclusion therefore holds even at the conventional index 0.

**Theorem 1.3 (Ten occurs second and is the only such multiple).**

$$\operatorname{seq}\left(2\right) = 10 \land (\forall m \in \mathbb{N}, (1 \le m \land m < 10) \implies ((\exists n \in \mathbb{N}, 1 \le n \land \operatorname{seq}\left(n\right) = 10 \cdot m) \iff m = 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumInConcatenation/DecimalMultiples.sequence_multiple_ten_classification` (`✓ std3`). ∎

*Citation.* M. F. Hasler (2026). *A359482, Proof by MFH*. URL: <https://oeis.org/w/index.php?title=A359482&oldid=1675118>.

*Commentary.*

The candidate 10 is positive, unused after the initial 1, and legal because 11 occurs in 110. The greedy minimum is at most 10, and the established tail bound is at least 10, so seq(2)=10. For 1<=m<10, the exclusion of 20 through 90 forces any occurring 10m to have m=1. Conversely index 2 supplies the positive index for m=1. These statements concern the original decimal sequence; no conclusion about hundreds or other bases follows.

## References

- Truth anchor: `D5/S3/Arith/SumInConcatenation/DecimalMultiples.legal_multiple_ten_iff`
- Truth anchor: `D5/S3/Arith/SumInConcatenation/DecimalMultiples.sequence_multiple_ten_classification`
- Truth anchor: `D5/S3/Arith/SumInConcatenation/DecimalMultiples.sequence_ne_multiple_ten`
- Dependency: [D5/S3/Arith/SumInConcatenation](../SumInConcatenation.md)
