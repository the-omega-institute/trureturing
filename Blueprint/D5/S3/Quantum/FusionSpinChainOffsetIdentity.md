# Fibonacci Fusion-Chain Offset Identity

## Abstract

The Fibonacci fusion-chain window dimension has an exact integer offset identity.

**Definition 1.1 (Fibonacci window dimension).**

Lean statement: `D5/S3/Quantum/FusionSpinChainOffsetIdentity.fusionDim`

*Formalization.* `D5/S3/Quantum/FusionSpinChainOffsetIdentity.fusionDim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer lift of the window algebra dimension is D(n) = F_(2n-1).

**Theorem 1.2 (Exact offset identity).**

Lean statement: `D5/S3/Quantum/FusionSpinChainOffsetIdentity.exact_offset_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/FusionSpinChainOffsetIdentity.exact_offset_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For integers n and k with |k| < n, the integer lift D(n) = F_(2n-1) satisfies D(n+k)D(n-k) - D(n)^2 = F_(2|k|)^2.

The proof applies the pinned integer Fibonacci Catalan identity with x = 2(n-k)-1 and a = 2k. The surrounding fusion-category, cut-algebra, FDQC, and QCA bridge remains outside this arithmetic declaration.

## References

- Truth anchor: `D5/S3/Quantum/FusionSpinChainOffsetIdentity.exact_offset_identity`
- Truth anchor: `D5/S3/Quantum/FusionSpinChainOffsetIdentity.fusionDim`
