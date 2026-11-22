# From the finite exponent sum to the normalized tail

## Abstract

Signed sixth and seventh prime-power contributions

**Theorem 1.1 (The finite signed correction).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff.abs_psi_sub_roots_add_theta_sixth_sub_seventh_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff.abs_psi_sub_roots_add_theta_sixth_sub_seventh_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtract θ(t) and the square, cube and fifth ψ cutoffs from ψ(t). The common finite exponent sum has coefficients -1, +1 and 0 at exponents six, seven and eight. Adding θ(t^(1/6)) and subtracting θ(t^(1/7)) leaves an absolute error at most 4 log(t)t^(1/9) for every t ≥ 2.

**Theorem 1.2 (The scaled tail and its uniform error).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff.sixth_seventh_normalized`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff.sixth_seventh_normalized` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under RH the two θ terms can be replaced by their powers with a pointwise error of order t^(1/8). Integrate against t^(-2) from x to infinity and multiply by sqrt(x). The sixth and seventh terms become -(6/5)x^(-1/3) and +(7/6)x^(-5/14). The resulting absolute error is bounded by a positive constant times x^(-3/8) for all x ≥ 5000^7.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff.abs_psi_sub_roots_add_theta_sixth_sub_seventh_le`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SeventhCutoff.sixth_seventh_normalized`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/Schoenfeld](../../Cryptids/Schoenfeld.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow](RHFifthWindow.md)
