# Saturation of maximal Sidon sets

## Abstract

A Sidon set that admits no further insertion inside the integers from one to N saturates that interval, so N is at most an explicit cubic polynomial in its cardinality.

A Sidon set inside the integers from one to N is maximal when every element of that interval outside it destroys the Sidon condition on insertion. Each such obstruction is an equation among old elements and the inserted one, so maximality forces the interval to be covered by the set together with the solution sets of those equations. Counting the cover in the two admissible shapes bounds N.

**Theorem 1.1 (The saturation inequality).**

Lean statement: `D5/S3/Arith/Additive/MaximalSidon.card_le_of_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/MaximalSidon.card_le_of_maximal` (`✓ std3`). ∎

*Citation.* Paul Erdős and András Sárközy and Vera T. Sós (1994). *On additive properties of general sequences*. DOI: [10.1016/0012-365X(94)00108-U](https://doi.org/10.1016/0012-365X(94)00108-U).

*Commentary.*

Let A be a Sidon subset of the integers from one to N such that no element x of that interval outside A leaves the insertion of x into A Sidon. Then N is at most the cardinality of A cubed plus that cardinality squared plus that cardinality. The proof first shows that a failed insertion of x produces either members a, b and c of A with x plus a equal to b plus c, or members b and c of A with twice x equal to b plus c. Cancellation in the naturals removes the cases where x occurs on both sides of the colliding equation, and the cases lying entirely inside A contradict the Sidon condition on A. Maximality then covers the interval by A, by the image of the triples of members of A under b plus c minus a, and by the image of the pairs of members of A under half of b plus c. The witness equalities make truncated subtraction and floor division exact at every point that has to be covered, so the two images do contain the points they are required to contain. The cardinality of a union is at most the sum of cardinalities, the cardinality of an image is at most the cardinality of its domain, and the interval from one to N has cardinality N, which gives the stated inequality. The displayed exponent three is the elementary bound recorded for this question; the explicit lower-order terms are the form proved here. No maximal Sidon set of that order is exhibited, so the question of whether one exists is untouched.

## References

- Truth anchor: `D5/S3/Arith/Additive/MaximalSidon.card_le_of_maximal`
- Dependency: [D5/S3/Arith/Additive/SidonSet](SidonSet.md)
