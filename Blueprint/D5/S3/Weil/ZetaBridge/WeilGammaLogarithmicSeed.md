# Gamma Logarithmic Seed Remainder

## Abstract

The singular logarithmic remainder of the existing polynomial Mellin seed has a proved finite endpoint integral, with its lower-endpoint singularity removed almost everywhere.

**Theorem 1.1 (Integrable arithmetic seed remainder and exact endpoint formula).**

Lean statement: `D5/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed.gamma_logarithmic_seed_remainder`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed.gamma_logarithmic_seed_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the already-owned cutPolynomialSeed(a,d,A), with complex coefficients, upper support exp(a), and 0<u<=exp(a). The actual integrand is t*(h(t)-h(u))/(t^2-u^2). Its numerator is combined before division. No boundary moment is set to zero and no quadrature or desired integral value is assumed.

The standard difference-of-powers formula identifies the quotient on (u,exp(a)] with sum_r A_r sum_{j<r} t^(2j+1)u^(2(r-1-j)). This is a continuous polynomial. Almost-everywhere equality on the interval proves integrability of the original singular expression, including degree zero and the degenerate interval. Finite integral linearity and the existing power-integral theorem give the complete endpoint sum.

The concrete consumer is the one-sided Gamma action after the actual prime-Mellin identity has cancelled the logarithmic seed. The full Gamma kernel realization, its endpoint logarithms, the positive shifted form, and the true-prolate C1 and jump-error transport are proved on paper in the existing RH volume and used by the directed interval verifier. They are not conclusions of this Lean declaration. No small residual, all-scale coercivity, Xi limit or RH is asserted. Lean elaboration and Scribe emission were not run.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilGammaLogarithmicSeed.gamma_logarithmic_seed_remainder`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining](WeilMellinPrimeIntertwining.md)
