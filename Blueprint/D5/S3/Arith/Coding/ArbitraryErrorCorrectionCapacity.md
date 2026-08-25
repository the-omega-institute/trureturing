# Arbitrary Error Correction Capacity

## Abstract

Disjoint radius-e Hamming balls force distance 2e+1 and the corresponding mixed-modulus capacity bound.

**Theorem 1.1 (Arbitrary error correction forces the capacity bound).**

$$\forall m: \mathbb{N} \to \mathbb{N}, \forall n, K, e \in \mathbb{N},\\{}(\forall i, j, i < j \land j < n \Rightarrow \operatorname{m}\left(i\right) < \operatorname{m}\left(j\right)) \land (\forall i, i < n \Rightarrow 2 \leq \operatorname{m}\left(i\right)) \land\\{}(\forall i, j, i < n \land j < n \land i \neq j \Rightarrow \gcd(\operatorname{m}\left(i\right), \operatorname{m}\left(j\right)) = 1) \land 2 \leq K \land\\{}(\forall x, y, r, (x < K \land y < K \land\operatorname{hammingDist}\left(r, \operatorname{residueWord}\left(m, n, x\right)\right) \leq e \land \operatorname{hammingDist}\left(r, \operatorname{residueWord}\left(m, n, y\right)\right) \leq e) \Rightarrow x = y)\\{}\Rightarrow \operatorname{MinDistanceAtLeast}\left(m, n, K, 2 \times e + 1\right) \land\\{}K \leq \operatorname{prefixProduct}\left(m, n - 2 \times e\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Coding/ArbitraryErrorCorrectionCapacity.arbitrary_error_correction_capacity_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correction premise is operational: any received word within e coordinates of two residue codewords forces their messages to coincide. Splitting the disagreement coordinates between two candidate words shows that their distance cannot be at most 2e.

The existing exact dynamic-range theorem then converts minimum distance 2e+1 into the product of the first n-2e moduli. The result does not need the ambient upper bound K at most the full modulus product.

## References

- Truth anchor: `D5/S3/Arith/Coding/ArbitraryErrorCorrectionCapacity.arbitrary_error_correction_capacity_bound`
- Dependency: [D5/S3/Arith/Coding/ResidueCodeDynamicRange](ResidueCodeDynamicRange.md)
