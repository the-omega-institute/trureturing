# The literal Carleman double integral on arbitrary complex L2 sources

## Abstract

Actual absolute Carleman double-integral domain and pi bound on half-line L2 sources.

**Theorem 1.1 (The literal Carleman double integral on half-line L2).**

Lean statement: `D5/S3/Weil/ZetaGamma/FormCore/CarlemanL2.carleman_actual_l2_domain`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaGamma/FormCore/CarlemanL2.carleman_actual_l2_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary complex positive-half-line L2 input, the actual absolute Carleman double integral is finite and is bounded by pi times its L2 mass. There is no compact-support, continuity, trace, or pre-assumed double-integrability condition.

The proof derives the true row integral of sqrt(s)/(sqrt(t)*(s+t)) from the actual Cauchy integral and proves product-measure integrability of the Schur majorant before applying an integral inequality. This theorem is consumed by the half-rate Hankel domain proof.

## References

- Truth anchor: `D5/S3/Weil/ZetaGamma/FormCore/CarlemanL2.carleman_actual_l2_domain`
