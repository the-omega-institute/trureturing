# Sum-Free Codes with Different Minimum Weights

## Abstract

Two first-order sum-free functions on the ternary plane have original codes with different attained minimum nonzero weights.

Let K be any finite field of cardinality q. Points are all n-tuples over K, including zero. An independent s-tuple of directions parametrizes an affine s-plane bijectively, so its function sum counts each point once. Sum-freedom requires every such vector sum to be nonzero. The original parity rows evaluate every reduced monomial with exponents less than q and total degree at most s(q minus one) minus one, followed by all n coordinates of the function. All monomials span the same Reed–Muller space as a generator basis and therefore define the same kernel.

Hamming weight counts nonzero entries. The minimum is the infimum of the weights of nonzero kernel words in the extended naturals; the zero code has value infinity. The assertion claim quantifies over every finite field, n at least two, one at most s at most n minus one, and every two sum-free functions, asserting equality of their minima. This is the minimum-weight component of the question immediately after Theorem 4.6 of Hou and Zhao, arXiv:2609.31489v1.

**Theorem 1.1 (Attained Minima Five and Four).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/hou-zhao-2026-sum-free-code-minimum-weight` (refuted) by `D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hou-zhao-2026-sum-free-code-minimum-weight","declaration_gid":"D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Take K equal to the ternary field, n equal to two and s equal to one. Set F(x,y) equal to (x squared minus y squared,2xy) and G(x,y) equal to (x squared,y squared). Both sums on every affine line are nonzero. The monomial rows specialize to one, x and y. Exact matrix identities reconstruct every original kernel word from four free coordinates. The 81 choices exclude all nonzero weights below five for F and below four for G. In point order (0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2), the words (0,0,1,0,0,1,1,1,2) and (1,2,0,2,1,0,0,0,0) lie in their respective kernels and attain five and four. Hence the minima differ.

The distance-five fact for F is also an instance of Carlet, Ding and Yuan (2005), equation (7), Theorem 7. In the extension with t squared equal to minus one, squaring has coordinates F, and the trace pairing spans exactly one, x, y and the coordinates of F. This identifies the extended trace-code dual with the original kernel. The unequal minima refute universal independence; complete ranges for the code parameters remain undetermined.

## References

- Truth anchor: `D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result`
- Dependency: [D5/S3/Arith/SumFreeCodeDimensionRefutation](SumFreeCodeDimensionRefutation.md)
