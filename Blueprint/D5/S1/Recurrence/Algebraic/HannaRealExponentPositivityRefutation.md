# Hanna's real-exponent positivity threshold is false

## Abstract

The source equation forces a negative degree-720 coefficient at t=8/3.

All series have real coefficients. PowerSeries.exp is the formal exponential series, PowerSeries.logOf is the formal logarithm of a series with constant coefficient one, and PowerSeries.subst is formal substitution. A real power G^t means substituting t • PowerSeries.logOf G into PowerSeries.exp ℝ. The primitive J has constant coefficient zero. PowerSeries.coeff j G is the ordinary degree-j coefficient, with j starting at zero. Multiplication by the positive EGF factor j! · 3^j preserves its sign.

**Definition 1.1 (The source integral equation).**

$$\forall t: \mathbb{R}, (\forall G: \operatorname{PowerSeries}\left(\mathbb{R}\right), (\operatorname{IsSourceSeries}\left(t, G\right) = ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(G\right) = 1) \land (\exists J: \operatorname{PowerSeries}\left(\mathbb{R}\right), ((\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(J\right) = 0) \land ((\operatorname{PowerSeries}.\operatorname{derivative}\left(J\right) = \operatorname{PowerSeries}.\operatorname{subst}\left((\operatorname{HSMul}.\operatorname{hSMul}\left(t, \operatorname{PowerSeries}.\operatorname{logOf}\left(G\right)\right)), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{R}\right)\right)) \land (G = \operatorname{PowerSeries}.\operatorname{subst}\left((G^{-1} \cdot J), \operatorname{PowerSeries}.\operatorname{exp}\left(\mathbb{R}\right)\right))))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.IsSourceSeries` (`✓ std3`).

*Citation.* Paul D. Hanna (2017). *OEIS A281186: real-exponent positivity conjecture*. URL: <https://oeis.org/A281186/internal>.

*Commentary.*

OEIS A281186, COMMENTS, revision 10 (unpaginated): "Conjecture: if G(x) = exp( 1/G(x) * Integral G(x)^t dx ) for some fixed real t, then G(x) will consist entirely of nonnegative coefficients iff t >= 8/3." The real parameter is t. The equations for J express the zero-constant formal primitive, and the constant coefficient of G is one. The source's PARI intformal program fixes the integration constant at zero.

**Definition 1.2 (The quantified positivity assertion).**

$$claim = (\forall t: \mathbb{R}, ((\exists G: \operatorname{PowerSeries}\left(\mathbb{R}\right), (\operatorname{IsSourceSeries}\left(t, G\right))) \land (\forall G: \operatorname{PowerSeries}\left(\mathbb{R}\right), ((\operatorname{IsSourceSeries}\left(t, G\right)) \implies ((\forall j: \mathbb{N}, (0 \le \operatorname{PowerSeries}.\operatorname{coeff}\left(j, G\right))) \iff (\frac{(8: \mathbb{R})}{3} \le t))))))$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2017). *OEIS A281186: real-exponent positivity conjecture*. URL: <https://oeis.org/A281186/internal>.

*Commentary.*

OEIS A281186, COMMENTS, revision 10 (unpaginated): "Conjecture: if G(x) = exp( 1/G(x) * Integral G(x)^t dx ) for some fixed real t, then G(x) will consist entirely of nonnegative coefficients iff t >= 8/3." The statement includes existence for each real t and the asserted equivalence for every source series G. Nonnegativity includes degree zero. The source EGF is "E.g.f.: A(x) = Sum_{n>=0} a(n) * x^n / (n! * 3^n)."

**Theorem 1.3 (Refutation at the boundary parameter).**

$$\neg (\forall t: \mathbb{R}, ((\exists G: \operatorname{PowerSeries}\left(\mathbb{R}\right), (\operatorname{IsSourceSeries}\left(t, G\right))) \land (\forall G: \operatorname{PowerSeries}\left(\mathbb{R}\right), ((\operatorname{IsSourceSeries}\left(t, G\right)) \implies ((\forall j: \mathbb{N}, (0 \le \operatorname{PowerSeries}.\operatorname{coeff}\left(j, G\right))) \iff (\frac{(8: \mathbb{R})}{3} \le t))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2017). *OEIS A281186: real-exponent positivity conjecture*. URL: <https://oeis.org/A281186/internal>.

*Commentary.*

At t=8/3, write y=PowerSeries.logOf G. Differentiation of the integral equation gives (1+y)y′=exp((5/3)y). An integer polynomial sequence begins with Q₀=1 and satisfies Qₙ=((5n+3)X+6−n)Qₙ₋₁+3(1+X)Q′ₙ₋₁ for n≥1. Induction on the derivative order gives (n+1)! · coeff(n+1,G)=(1/3)^n · coeff(0,Qₙ). Exact integer reduction proves coeff(0,Q₇₁₉)<0. The asserted existence supplies G, and the asserted nonnegativity at 8/3 contradicts its degree-720 coefficient. This argument does not separately establish existence, uniqueness, the least negative degree, or a corrected threshold.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.IsSourceSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaRealExponentPositivityRefutation.result`
