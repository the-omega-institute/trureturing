# Schwarzian inference from ODE and Abel data

## Abstract

An Abel ratio of a nonvanishing second-order ODE solution has actual third-order regularity and an exact Schwarzian.

**Definition 1.1 (The actual derivative quotient).**

Lean statement: `D5/S3/Analytic/AbelRatioSchwarzian.preSchwarzian`

*Formalization.* `D5/S3/Analytic/AbelRatioSchwarzian.preSchwarzian` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions: Schwarzian derivatives and the hypergeometric differential equation*. URL: <https://dlmf.nist.gov/1.13>.

*Commentary.*

For a complex function t, preSchwarzian(t,x) is literally deriv(deriv t)(x) divided by deriv t(x). Nonvanishing and regularity are conclusions of the inference, rather than part of this definition.

**Definition 1.2 (The classical Schwarzian convention).**

Lean statement: `D5/S3/Analytic/AbelRatioSchwarzian.schwarzian`

*Formalization.* `D5/S3/Analytic/AbelRatioSchwarzian.schwarzian` (`✓ std3`).

*Citation.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions: Schwarzian derivatives and the hypergeometric differential equation*. URL: <https://dlmf.nist.gov/1.13>.

*Commentary.*

S(t)=t'''/t'-(3/2)(t''/t') squared, with all three derivatives the actual complex derivatives. This is the convention of DLMF 1.13.20.

**Theorem 1.3 (The inference, including second and third derivatives).**

Lean statement: `D5/S3/Analytic/AbelRatioSchwarzian.abel_ratio_schwarzian`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/AbelRatioSchwarzian.abel_ratio_schwarzian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions: Schwarzian derivatives and the hypergeometric differential equation*. URL: <https://dlmf.nist.gov/1.13>.

*Commentary.*

On any open complex set U, assume y and its actual first derivative are differentiable, y is nonzero, p is differentiable, the nonzero Abel factor W has derivative -pW, t has derivative W/y squared, and y''+py'+qy=0. Then t' is nonzero. Writing L=y'/y and G=-p-2L, the theorem supplies HasDerivAt t' (G t'), and HasDerivAt t'' ((-p'-2(-pL-q-L squared)+G squared)t'). It also proves t''/t'=G and S(t)=2q-p'-p squared/2.

The proof first identifies t' with W/y squared on a neighborhood inside U. Quotient differentiation and the ODE give L'=-pL-q-L squared. A second neighborhood identity t''=Gt' then permits differentiation to the actual third derivative. No derivative of q or third derivative of y is a premise. The original half-binomial period is the live consumer. This formalizes a classical calculation and makes no literature novelty claim.

## References

- Truth anchor: `D5/S3/Analytic/AbelRatioSchwarzian.abel_ratio_schwarzian`
- Truth anchor: `D5/S3/Analytic/AbelRatioSchwarzian.preSchwarzian`
- Truth anchor: `D5/S3/Analytic/AbelRatioSchwarzian.schwarzian`
