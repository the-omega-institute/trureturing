# Pfaff Jumps and the Negative Real Nome

## Abstract

Exact Pfaff jumps of the original complementary ratio and its signed charge nome.

With r = k² the supplier's normalized period is P(r) = 2K(k)/π. DLMF 19.7.2a and 19.7.3b give the two jump identities by taking the period ratio. For the principal k with Re k > 0, the upper sign in 19.7.3b applies to Im(k²) > 0 and the lower sign to Im(k²) < 0, as credited there to Fettis. DLMF 22.2.1 fixes the nome convention q = exp(−π K′(k)/K(k)). The Lean proofs use the literal Euler period and its compiled Pfaff transformation (DLMF 15.8.1 at a = b = 1/2 and c = 1).

**Theorem 1.1 (Exact upper-half-plane jump).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.tau_pfaff_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.tau_pfaff_upper` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Hypergeometric function, Pfaff transformation*. URL: <https://dlmf.nist.gov/15.8.E1>.

*Commentary.*

For Im r > 0, τ(r) = τ(r/(r − 1)) + 1. The Pfaff period square and the chain rule make the difference constant. The map r ↦ 1/(1 − r) fixes u = (1 + i√3)/2. Differentiating the reciprocal ratio identity there and cancelling the nonzero quotient derivative gives τ(u)² = u². The positive imaginary parts give τ(u) = u, and u + 1/u = 1 fixes the addend.

**Theorem 1.2 (Exact lower-half-plane jump).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.tau_pfaff_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.tau_pfaff_lower` (`✓ std3`). ∎

*Citation.* NIST Digital Library of Mathematical Functions (2026). *Hypergeometric function, Pfaff transformation*. URL: <https://dlmf.nist.gov/15.8.E1>.

*Commentary.*

For Im r < 0, τ(r) = τ(r/(r − 1)) − 1. The Pfaff map interchanges the half-planes and is an involution, so the upper identity gives the lower one.

**Definition 1.3 (Signed Pfaff nome).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negativeChartNome`

*Formalization.* `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negativeChartNome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At r use minus the exponential of iπτ(r/(r − 1)).

**Theorem 1.4 (Holomorphic charge factors).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negative_real_nome_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negative_real_nome_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every real x < 0 has an open complex neighborhood on which the signed Pfaff nome is holomorphic and has modulus strictly below one. On the overlap with the double slit it agrees with exp(iπτ(r)), since both signed unit jumps contribute −1. Every natural power extends on the same neighborhood with multiplier (−1)ᵐ in the Pfaff chart. This supplies the charge factor at natural charge energy m. Full crossing also requires matching the actual source and oscillator factors and establishing normal convergence.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negativeChartNome`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.negative_real_nome_extension`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.tau_pfaff_lower`
- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialPfaffNome.tau_pfaff_upper`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialSlitPeriod](OriginalHalfBinomialSlitPeriod.md)
