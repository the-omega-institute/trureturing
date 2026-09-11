# Polynomial Mellin Window

## Abstract

An actual finite polynomial arithmetic Mellin window has an integrable complex Fourier kernel and an exact finite endpoint transform.

This source reuses Zeta23.paperFT with kernel exp(i*z*x). For h(t)=sum_{r<d} A_r*t^(2*r), the arithmetic window is 4*exp(x/2)*sum_{1<=m<=M, m*exp(x)<=exp(a)} h(m*exp(x)) on [-a,a], with zero extension. The chosen Ioc endpoints give the same Lebesgue Fourier transform. The finite polynomial is a concrete approximation of the regular prolate modes, whose independent spectral certification is explained in the source analysis.

**Definition 1.1 (Fourier-shifted monomial rate).**

$$\operatorname{mellinRate}(r, z)=\operatorname{add}(\operatorname{mul}(2, r), \operatorname{div}(1, 2), \operatorname{mul}(i, z))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.mellinRate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

r is natural and z complex; the exponent is 2*r+1/2+i*z.

**Definition 1.2 (One arithmetic monomial).**

$$\operatorname{mellinMonomial}(a, m, r, x)=\operatorname{IndicatorIoc}(-a, a-\operatorname{log}(m), \operatorname{mul}(\operatorname{pow}(m, \operatorname{mul}(2, r)), \operatorname{exp}(\operatorname{mul}(\operatorname{mellinRate}(r, 0), x))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.mellinMonomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The formula uses a real interval and a complex exponential. It is specified before any Fourier evaluation.

**Definition 1.3 (Finite polynomial arithmetic synthesis).**

$$\operatorname{apply}(\operatorname{polynomialMellinWindow}(a, M, d, A), x)=\operatorname{mul}(4, \operatorname{SumIcc}(1, M, \operatorname{SumRange}(d, \operatorname{mul}(\operatorname{apply}(A, r), \operatorname{mellinMonomial}(a, m, r, x)))))$$

*Formalization.* `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.polynomialMellinWindow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sums are over m=1,...,M and r=0,...,d-1. The factor four matches the calibrated Xi Mellin normalization in the existing volume.

**Theorem 1.4 (Exact polynomial identity).**

$$\operatorname{mellinMonomial}(a, m, r, x)=\operatorname{IndicatorIoc}(-a, a-\operatorname{log}(m), \operatorname{mul}(\operatorname{exp}(\operatorname{div}(x, 2)), \operatorname{pow}(\operatorname{mul}(m, \operatorname{exp}(x)), \operatorname{mul}(2, r))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.mellin_monomial_polynomial_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exponential form equals exp(x/2)*(m*exp(x))^(2*r) on the actual support. The proof uses exponential addition and natural powers; the half-power is retained.

**Theorem 1.5 (Actual Fourier integrability).**

$$\operatorname{Integrable}(\operatorname{mul}(\operatorname{apply}(\operatorname{polynomialMellinWindow}(a, M, d, A), x), \operatorname{exp}(\operatorname{mul}(i, z, x))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.polynomial_mellin_fourier_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a, natural M,d, complex coefficient family A and complex z, the actual Fourier integrand is integrable. Compact interval continuity proves each summand integrable, followed by finite linearity. This excludes totalized nonintegrable Fourier values.

**Theorem 1.6 (Quadrature-free Fourier evaluation).**

$$\operatorname{And}(\operatorname{ForAllIcc}(1, M, \operatorname{LessEqual}(\operatorname{log}(m), \operatorname{mul}(2, a))), \operatorname{Less}(\operatorname{Im}(z), \operatorname{div}(1, 2)))\Rightarrow \operatorname{paperFT}(\operatorname{polynomialMellinWindow}(a, M, d, A), z)=\operatorname{mul}(4, \operatorname{SumIcc}(1, M, \operatorname{SumRange}(d, \operatorname{mul}(\operatorname{apply}(A, r), \operatorname{pow}(m, \operatorname{mul}(2, r)), \operatorname{div}(\operatorname{exp}(\operatorname{mul}(\operatorname{mellinRate}(r, z), a-\operatorname{log}(m)))-\operatorname{exp}(\operatorname{mul}(\operatorname{mellinRate}(r, z), -a)), \operatorname{mellinRate}(r, z))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.polynomial_mellin_window_paperFT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume log(m)<=2*a for each included positive integer m and Im(z)<1/2. Every rate has positive real part, so no denominator is zero. The proof identifies the Fourier integrand on each arithmetic interval, uses the existing complex-exponential integral theorem, and interchanges only finite sums with proved integrable summands. No quadrature hypothesis or unknown prolate/Weil eigenvector is supplied. The numerical consumer independently certifies prolate eigenpairs and their complete Legendre tail. The all-scale arithmetic ground-model comparison remains open; this source does not prove the prolate spectral theorem, Xi convergence or RH.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.mellinMonomial`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.mellinRate`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.mellin_monomial_polynomial_value`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.polynomialMellinWindow`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.polynomial_mellin_fourier_integrable`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilPolynomialMellinWindow.polynomial_mellin_window_paperFT`
