# Primorial Witness Bound

## Abstract

A sufficiently large first-prime product bounds the first distinguishing-prime index.

**Theorem 1.1 (The first distinguishing prime lies in a sufficiently large prefix).**

$$\forall x \in \mathbb{Z}, y \in \mathbb{Z}, r \in \mathbb{N},\; \left(x \ne y \land \left|x - y\right| < \operatorname{primePrefixProduct}\left(r\right)\right) \Rightarrow \operatorname{horizontalWitnessComplexity}\left(x, y\right) \le r$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/PrimorialWitnessBound.primorial_witness_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct integers x and y, horizontalWitnessComplexity is the least positive one-based index j for which the j-th prime does not divide x minus y. The imported primePrefixProduct is the product of the first r primes.

If the complexity exceeded r, every prime in the first r positions would divide the difference. Their pairwise coprimality would then make the entire prefix product divide that difference.

A positive divisor of a nonzero integer has size at most the absolute value of that integer, contradicting the strict prefix-product bound.

## References

- Truth anchor: `D5/S3/Arith/Coding/PrimorialWitnessBound.primorial_witness_bound`
- Dependency: [D5/S3/Arith/Coding/HorizontalCompletenessDepth](HorizontalCompletenessDepth.md)
