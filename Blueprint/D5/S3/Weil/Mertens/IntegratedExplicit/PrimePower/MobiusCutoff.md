# The arithmetic error and its integrated bound

## Abstract

Möbius truncation of the Chebyshev root sum

**Theorem 1.1 (A geometric bound uniform in the truncation order).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff.chebyshev_mobius_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff.chebyshev_mobius_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For t ≥ 2 and an integer m ≥ 2, approximate θ(t) − ψ(t) by the finite sum of μ(n)ψ(t^(1/n)) over 2 ≤ n ≤ m. The absolute error is at most 2(log 4 + 4)(1 + (m + 1)/log 2)t^(1/(m+1)). Finite Möbius inversion cancels the divisor multiplicities at a common cutoff. A root term of degree n vanishes below t = 2^n, and above that threshold the global bound for ψ gives a geometric bound in n.

**Theorem 1.2 (The normalized prime-only tail).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff.integrated_mobius_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff.integrated_mobius_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For x ≥ 2 and m ≥ 2, subtract the complete Chebyshev tail and the sum of the μ(n)-weighted root integrals from the prime-only tail. Each root integral uses the kernel ψ(t^(1/n))/t² on (x,∞). The absolute residual after multiplication by sqrt(x) is at most 2(log 4 + 4)(1 + (m + 1)/log 2) times x^(1/(m+1) − 1/2) divided by 1 − 1/(m+1).

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff.chebyshev_mobius_truncation`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/MobiusCutoff.integrated_mobius_truncation`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents](FifthExponents.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/RHFifthWindow](RHFifthWindow.md)
