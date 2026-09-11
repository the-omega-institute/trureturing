# Constant Blocks with a Common Sum

## Abstract

The divisor sum of partition counts with an equal-sum constant-block decomposition counts all such block systems.

**Theorem 1.1 (The A383093 divisor identity).**

$$\forall n\in\mathbb{N}, 0<n \implies \sum_{d\mid n}a(d) = s(n)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity.capable_divisor_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman (2025). *A383093 — partitions admitting constant blocks with a common sum*. URL: <https://oeis.org/A383093>.

*Commentary.*

Here a(d) counts unlabeled integer partitions of weight d for which a decomposition into constant blocks with a common sum exists. The function s(n) counts all block multisets of weight n, as in A323774. The OEIS entry states this identity as a conjecture.

A system is recorded by its positive common sum D and a multiset of positive block values dividing D. Each occurrence of x denotes one block of D/x copies of x. The proof checks flattening, weight, and unique recovery of this multiset from the partition and D. The two counts are defined independently.

For a flattened partition let L be the lcm of its support. Every admissible common sum is tL. The equal-sum condition forces t to divide every multiplicity. Dividing those multiplicities by t preserves the support and produces a capable partition of weight n/t with common sum L. Conversely, scaling a capable partition of weight d by n/d gives a system of weight n. The lcm of the unchanged support recovers the scaling factor, making these constructions inverse. Taking finite cardinalities proves the identity for positive n. The empty system is counted separately.

## References

- Truth anchor: `D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity.capable_divisor_sum`
