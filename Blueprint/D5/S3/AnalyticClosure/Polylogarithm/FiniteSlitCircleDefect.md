# FiniteSlitCircleDefect

## Abstract

The actual patched outer Cauchy contribution is integrable and obeys the same source bound for every natural index.

**Definition 1.1 (The single cut point).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.outerIntegrand`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.outerIntegrand` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

For A : Complex to Complex, real R and natural n, the integrand is zero at z=R and A(z)/z^(n+1) elsewhere.

**Definition 1.2 (The positively oriented outer contribution).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.outerCoefficient`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.outerCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

outerCoefficient is the actual circle integral of outerIntegrand about zero with radius R, multiplied by the inverse of 2 pi i.

**Definition 1.3 (The logarithmic pullback).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.upperPullback`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.upperPullback` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

upperPullback P n w equals P(exp w)/(exp w)^n. The exponent n retains the cancellation of one denominator power by the exponential Jacobian.

**Definition 1.4 (The oriented upper rectangle).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.upperRectangleBalance`

*Formalization.* `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.upperRectangleBalance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

upperRectangleBalance is the exact equation bottom minus top plus i times right minus i times left equals zero, for upperPullback on the rectangle from log(1/2) to log(R) and from angle zero to pi.

**Theorem 1.5 (All compositions and all natural indices).**

Lean statement: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.result`

*Proof.* Machine-checked in Lean as `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ce Xu and Jianqiang Zhao (2026). *Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers*. DOI: [10.48550/arXiv.2609.11072](https://doi.org/10.48550/arXiv.2609.11072). URL: <https://arxiv.org/html/2609.11072v1>.

*Commentary.*

Every positive head, finite positive-entry tail and positive ell has the SAME R0, rho, R, upper and B supplied by FiniteSlitCompositionMoments.result. The actual reciprocal is analytic on the slit disk, agrees with the original normalized disk reciprocal and retains its removable value at zero. The upper bank extends it continuously to the closed upper half disk of radius R. The extension equals the reciprocal on omega and the same bank on the cut.

For every natural n, including zero, the patched outer integrand is CircleIntegrable, the imaginary bank moment is IntervalIntegrable from 1 to R, and norm(outerCoefficient)<=B/R^n. The bound uses the original B, independent of n. Analytic continuity off the single cut point proves angular measurability; the sphere bound then proves actual integrability. The circle norm theorem gives the stated exact bound.

The extension is pasted across two closed sets separated by delta=(rho+R-1)/2. The far set lies in omega; the near set uses upper-bank continuity. Their overlap agrees by the actual bank matching law.

For every natural n the extension also satisfies upperRectangleBalance. Its proof applies rectangular Goursat to the constructed continuous extension; in the open rectangle the exponential image has positive imaginary part and the pullback is analytic. The full-circle finite-slit coefficient identity and its relation to iterated derivatives remain unproved here. No source coefficient sign follows from this result alone. Exact ordinary formal-inverse realization, all fixed positive j and the strict admissible binomial lower bound remain separate obligations. The full Xu--Zhao problem remains open.

## References

- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.outerCoefficient`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.outerIntegrand`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.result`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.upperPullback`
- Truth anchor: `D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCircleDefect.upperRectangleBalance`
- Dependency: [D5/S3/AnalyticClosure/Polylogarithm/FiniteSlitCompositionMoments](FiniteSlitCompositionMoments.md)
