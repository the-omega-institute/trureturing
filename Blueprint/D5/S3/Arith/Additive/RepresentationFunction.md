# Representation functions of a finite set

## Abstract

Counting the ordered pairs of a finite set by their sum distributes the square of the cardinality over the reachable sums.

The representation function records how many ways a number is a sum of two members of a set. Both the ordered and the unordered count are kept, since additive questions are stated in either convention; the total mass identity below is the ordered one, where every pair is counted once.

**Definition 1.1 (The ordered count).**

Lean statement: `D5/S3/Arith/Additive/RepresentationFunction.repCount`

*Formalization.* `D5/S3/Arith/Additive/RepresentationFunction.repCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set A of naturals and a natural n, repCount A n is the number of ordered pairs in the product of A with itself whose two entries sum to n. Repeated summands are counted, and the pair with entries exchanged is counted separately.

**Definition 1.2 (The unordered count).**

Lean statement: `D5/S3/Arith/Additive/RepresentationFunction.repCountUnordered`

*Formalization.* `D5/S3/Arith/Additive/RepresentationFunction.repCountUnordered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same count restricted to pairs whose first entry is at most the second, so each unordered pair contributes once while a repeated summand still contributes. This is the convention in which the Sidon condition reads as the count never exceeding one.

**Theorem 1.3 (Total mass).**

Lean statement: `D5/S3/Arith/Additive/RepresentationFunction.repCount_total_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/RepresentationFunction.repCount_total_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If A is contained in the naturals below N plus one, then summing repCount A n over n below twice N plus one gives the square of the cardinality of A. Every ordered pair from A has its sum in that range, so the sum counts the fibres of the addition map on the product of A with itself; the fibres partition that product, whose cardinality is the square of the cardinality of A.

## References

- Truth anchor: `D5/S3/Arith/Additive/RepresentationFunction.repCount`
- Truth anchor: `D5/S3/Arith/Additive/RepresentationFunction.repCountUnordered`
- Truth anchor: `D5/S3/Arith/Additive/RepresentationFunction.repCount_total_mass`
