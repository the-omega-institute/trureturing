# Canonical Gaussian period correction and the native quotient

## Abstract

The canonical Gaussian correction is determined by the actual native period-ratio derivative quotient.

**Theorem 1.1 (The exact correction bridge in both directions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianProjectiveCorrection.original_correction_projective`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianProjectiveCorrection.original_correction_projective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions: Schwarzian derivatives and the hypergeometric differential equation*. URL: <https://dlmf.nist.gov/1.13>.

*Commentary.*

For every complex r in the full open lens, use exactly OriginalGaussianFiniteCandidateModes.ell=P'/P and its canonical k=r(1-r)ell. For the literal tau=iP(1-r)/P(r), g is the actual derivative quotient deriv(deriv tau)/deriv tau. Then g=-(1-2r+2k)/(r(1-r)), and k=(2r-1)/2-r(1-r)g/2, with no additional premises.

The proof consumes the native period theorem's actual quotient inference and the canonical definitions of ell and k. It solves the resulting identity using the nonzero lens factors. The correction is thus attached to the existing Gaussian object, rather than a replacement period or an assumed projective connection. No all-mode kernel, operator transport, stress tensor, anomaly or physical spacetime conclusion is included.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianProjectiveCorrection.original_correction_projective`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialProjective](../../../Analytic/OriginalHalfBinomialProjective.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteCandidateModes](OriginalGaussianFiniteCandidateModes.md)
