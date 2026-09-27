# Squarefree Numbers Have No Partition Whose Parts and Multiplicities Agree in Mean

## Abstract

A squarefree number above one has no partition whose parts and whose multiplicities share a mean, because squarefreeness turns the mean condition into a count of distinct parts that exceeds the count of parts unless every multiplicity is one.

**Definition 1.1 (The conjectured exclusion).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; ((squarefree n) \land (1 < n)) \Rightarrow (\forall y \in Partitions(n),\; total(y) \cdot distinct(y) \ne parts(y)^{2}))$$

*Formalization.* `D5/S3/Combinatorics/SquarefreeMeanPartition.claim` (`✓ std3`).

*Citation.* Gus Wiseman (2023). *OEIS A360070, Numbers for which there exists an integer partition such that the parts have the same mean as the multiplicities*. URL: <https://oeis.org/A360070>.

*Commentary.*

A partition is presented by its set of distinct parts together with a multiplicity function. The mean of the parts is the total divided by the number of parts, and the mean of the multiplicities is the number of parts divided by the number of distinct parts. Equating them and clearing denominators gives the total times the number of distinct parts equal to the square of the number of parts; both denominators are positive for a partition of a positive number, so nothing is lost and the statement stays inside the naturals. The bound above one is the source's own, and it is needed: at one the single-part partition has both means equal to one.

**Theorem 1.2 (The exclusion holds).**

$$\forall n \in \mathrm{Nat},\; ((squarefree n) \land (1 < n)) \Rightarrow (\forall y \in Partitions(n),\; total(y) \cdot distinct(y) \ne parts(y)^{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SquarefreeMeanPartition.result` (`✓ std3`). ∎

*Resolves.* `Problems/squarefree-mean-partition` (proved) by `D5/S3/Combinatorics/SquarefreeMeanPartition.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"squarefree-mean-partition","declaration_gid":"D5/S3/Combinatorics/SquarefreeMeanPartition.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2023). *OEIS A360070, Numbers for which there exists an integer partition such that the parts have the same mean as the multiplicities*. URL: <https://oeis.org/A360070>.

*Commentary.*

Squarefreeness enters once. The total divides the square of the number of parts, so for a squarefree total it divides the number of parts; write the quotient. Substituting and cancelling the positive total leaves the number of distinct parts equal to the total times the square of that quotient. Every multiplicity is at least one, so the distinct parts are at most as many as the parts, which forces the quotient to be one, and then the number of parts and the number of distinct parts both equal the total. Those two being equal forces every multiplicity to be exactly one, so the total is the sum of that many distinct positive parts; one of them exceeding one would push the sum past the total, so every part is one, so the distinct parts number at most one, against their number being the total, which exceeds one.

## References

- Truth anchor: `D5/S3/Combinatorics/SquarefreeMeanPartition.claim`
- Truth anchor: `D5/S3/Combinatorics/SquarefreeMeanPartition.result`
