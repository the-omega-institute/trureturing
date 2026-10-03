# Endpoint Formulas for Periodic Continuants

## Abstract

The period-four signed weights and period-two Narayana weights yield endpoint formulas in one second-order recurrence.

**Theorem 1.1 (Endpoints for the signed weights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.minus_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.minus_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Let t and z belong to any commutative ring. Define F_0 = 0, F_1 = 1 and F_{n+2} = (1 - (1 + t^2)z^2)F_{n+1} - t^2 z^4 F_n. Let P and Q satisfy the continuant recurrence with coefficients repeating z, tz, -z, -tz and initial values (0, 1) and (1, 1), respectively. For every nonnegative integer m, P_{4m+1} = F_{m+1} + (z + z^2)F_m, Q_{4m+1} = F_{m+1} - tz^2 F_m, P_{4m+2} = F_{m+1} + tz^2 F_m, and Q_{4m+2} = F_{m+1} - z(F_{m+1} + t^2 z^2 F_m).

**Theorem 1.2 (Endpoints for the squared Narayana weights).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.plus_endpoints`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.plus_endpoints` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

Let t and z belong to any commutative ring. Define F_0 = 0, F_1 = 1 and F_{n+2} = (1 - (1 + t^2)z^2)F_{n+1} - t^2 z^4 F_n. Let P and Q satisfy the continuant recurrence with coefficients alternating z^2 and t^2 z^2 and initial values (0, 1) and (1, 1), respectively. For every nonnegative integer k, P_{2k+1} = F_{k+1} + z^2 F_k, Q_{2k+1} = F_{k+1}, P_{2k} = F_k, and Q_{2k} = F_{k+1} + t^2 z^2 F_k.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.minus_endpoints`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra.plus_endpoints`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductContinuants](CiglerStripProductContinuants.md)
