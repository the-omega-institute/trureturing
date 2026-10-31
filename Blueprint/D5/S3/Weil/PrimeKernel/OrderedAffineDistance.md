# Ordered Affine Distance Energy

## Abstract

The literal ordered affine distance kernel has an exact complex cut-energy decomposition and a sharp finite positive-definiteness threshold.

**Theorem 1.1 (The literal distance kernel is positive definite exactly above the endpoint threshold).**

Lean statement: `D5/S3/Weil/PrimeKernel/OrderedAffineDistance.posdef_iff_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/PrimeKernel/OrderedAffineDistance.posdef_iff_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a monotone finite ordered family of real nodes, the matrix entry is literally L-|t_i-t_j|. The proof expands each ordered distance into the intervening gaps and rewrites every crossing cut through the complex prefix and suffix norm squares.

The resulting identity is valid for arbitrary complex coefficients, including the one-node case. In centered form it is (L-D/2)|M|² plus twice the positive gap-weighted sum of |C_k-M/2|². Strictly increasing nodes make every gap positive; a zero-total nonzero coefficient vector has a nonzero proper prefix.

The endpoint two-coordinate restriction gives the converse threshold. This finite theorem concerns the literal distance matrix only. It does not prove the analytic actual-prime-kernel mixture bound K>=rA or global Riemann-hypothesis implications.

The ordered cut decomposition and the centered complex energy are the new content consumed by the sharp criterion; generic positive-matrix hypotheses are not used as a substitute.

## References

- Truth anchor: `D5/S3/Weil/PrimeKernel/OrderedAffineDistance.posdef_iff_threshold`
