# Original Signed Fourier Regularity

## Abstract

Both jumps of the literal zero extension remain present. Each boundary strip has energy h/L, and the overlap energy is retained separately in the exact norm identity. The square-root h majorant is a line L2 statement, not a global line H1 assertion. The singular Gamma-density/form-domain and strong mixed-tail assembly remain separate.

Both jumps of the literal zero extension remain present. Each boundary strip has energy h/L, and the overlap energy is retained separately in the exact norm identity. The square-root h majorant is a line L2 statement, not a global line H1 assertion. The singular Gamma-density/form-domain and strong mixed-tail assembly remain separate.

**Definition 1.1 (lineMode).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.lineMode`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.lineMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the original Ioc zero extension of the normalized profile, evaluated as a line function.

**Definition 1.2 (translationSquaredNorm).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translationSquaredNorm`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translationSquaredNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal squared L2 displacement is the integral on the real line of the squared norm of F_n(x)-F_n(x-h).

**Theorem 1.3 (boundary strip energies).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.boundary_strip_energies`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.boundary_strip_energies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<=h<=L the left strip (-L/2,-L/2+h] and the right strip (L/2,L/2+h] each contribute exactly h/L. Neither boundary jump is discarded.

**Theorem 1.4 (translation squared norm).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translation_squared_norm`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translation_squared_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<=h<=L the squared gap is 2*h/L+2*(1-h/L)*(1-cos(w_n*h)). The correlation proof uses the two-strip mass term, including n=0, h=0 and h=L.

**Theorem 1.5 (translation squared norm le).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translation_squared_norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translation_squared_norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact gap is at most 2*h/L+w_n squared*h squared. The linear term remains for the zero mode.

**Definition 1.6 (displacedMode).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedMode`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A line L2 representative is constructed from proved MemLp of the literal zero extension and its measure-preserving translate.

**Definition 1.7 (displacedHead).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedHead`

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedHead` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite complex combination is formed on line L2 using every signed retained mode.

**Theorem 1.8 (finite head translation bound).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.finite_head_translation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.finite_head_translation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite head gap is bounded by sqrt(2/L)*sum(norm(v_n))*sqrt(h)+sum(norm(v_n)*abs(w_n))*h for 0<=h<=L.

**Theorem 1.9 (finite head translation bound l2).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.finite_head_translation_bound_l2`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.finite_head_translation_bound_l2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite Cauchy--Schwarz gives [sqrt(2*card(S)/L)*sqrt(h)+sqrt(sum(w_n squared))*h]*sqrt(sum(norm(v_n) squared)). Empty sets and all signed zero modes are included.

**Theorem 1.10 (displacedHead ae).**

Lean statement: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedHead_ae`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedHead_ae` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constructed finite L2 sum agrees almost everywhere with the displacement of the actual original zero-extended finite complex profile, rather than a periodic profile.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.boundary_strip_energies`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedHead`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedHead_ae`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.displacedMode`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.finite_head_translation_bound`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.finite_head_translation_bound_l2`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.lineMode`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translationSquaredNorm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translation_squared_norm`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalSignedFourierRegularity.translation_squared_norm_le`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalSignedPrimeFourier](OriginalSignedPrimeFourier.md)
