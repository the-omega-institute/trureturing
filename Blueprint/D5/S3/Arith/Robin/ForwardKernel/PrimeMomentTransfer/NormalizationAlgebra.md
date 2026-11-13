# Moment normalization algebra

## Abstract

Exact normalization identities for positive interval lengths and logarithmic scales.

**Theorem 1.1 (Powers of the standard deviation).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.normalizer_powers`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.normalizer_powers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive H and L, both (HL)^(3/2) and (HL)^2 are positive. The third and fourth powers of the square root of HL equal these two quantities, respectively.

**Theorem 1.2 (Cubic formal normalization).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.cubic_formal_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.cubic_formal_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive H and L and any real E, dividing E(HL)^(3/2)+HL^2 by (HL)^(3/2) gives E plus the square root of L/H.

**Theorem 1.3 (Fourth formal normalization).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.fourth_formal_ratio`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.fourth_formal_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive H and L and any real E, dividing EH^2L^2+H^2L by (HL)^2 gives E+1/L.

**Theorem 1.4 (Cubic arithmetic normalization).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.arithmetic_ratio_three`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.arithmetic_ratio_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive N, H and log N and any real epsilon, N^(1/2+epsilon)H^3 divided by N(H log N)^(3/2) equals N^(-1/2+epsilon)H^(3/2)(log N)^(-3/2).

**Theorem 1.5 (Fourth arithmetic normalization).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.arithmetic_ratio_four`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.arithmetic_ratio_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive N, H and log N and any real epsilon, N^(1/2+epsilon)H^4 divided by N(H log N)^2 equals N^(-1/2+epsilon)H^2(log N)^(-2).

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.arithmetic_ratio_four`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.arithmetic_ratio_three`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.cubic_formal_ratio`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.fourth_formal_ratio`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra.normalizer_powers`
