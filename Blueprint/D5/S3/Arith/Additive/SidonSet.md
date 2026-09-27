# Sidon sets and the difference-counting bound

## Abstract

A Sidon subset of the integers from one to N obeys the classical difference-counting cardinality bound.

A set is Sidon when a sum of two of its elements determines the pair of summands up to their order. Repeated summands are allowed, so the condition is stated on sums rather than on differences; over the naturals this avoids reading a truncated subtraction as a signed difference.

**Definition 1.1 (Sidon sets).**

Lean statement: `D5/S3/Arith/Additive/SidonSet.IsSidon`

*Formalization.* `D5/S3/Arith/Additive/SidonSet.IsSidon` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsSidon A holds when, for members a, b, c and d of A, the equality of a plus b with c plus d forces a to equal c and b to equal d, or a to equal d and b to equal c.

**Theorem 1.2 (The cardinality bound).**

Lean statement: `D5/S3/Arith/Additive/SidonSet.card_mul_card_sub_one_le`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/SidonSet.card_mul_card_sub_one_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite Sidon set A inside the integers from one to N, the product of the cardinality of A with one less than that cardinality is at most twice N minus one. The proof sends an ordered pair of distinct members of A to a sign together with the magnitude of their difference, which lands in the integers from one to N minus one. The Sidon condition makes that map injective, and counting the target supplies the factor two. The factor is not removable: the pair one and two inside the interval up to two is a Sidon set for which the bound without it fails.

## References

- Truth anchor: `D5/S3/Arith/Additive/SidonSet.IsSidon`
- Truth anchor: `D5/S3/Arith/Additive/SidonSet.card_mul_card_sub_one_le`
