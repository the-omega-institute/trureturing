# A quadratic majorant and weighted moment comparison

## Abstract

A quadratic tangent interpolant bounds the logarithmic function on positive support up to its upper node, and its finite weighted sum depends only on mass, mean, and centered second moment.

Write f(t)=log(1-exp(-t)). All scalar parameters and weights are real. The index set I is any finite type; its cardinality need not equal k. A weighted sum means the sum over all i in I of w(i) times the displayed value. The parameter k is a natural number, and W denotes the weighted centered second moment, without division by the total mass.

$\operatorname{f}\left(t\right)=\log(1-\exp(-t))$

**Definition 1.1 (The quadratic coefficient).**

$$a=\frac{\operatorname{f}\left(H\right)-\operatorname{f}\left(L\right)-\operatorname{deriv}\left(f, L\right)(H-L)}{(H-L)^{2}}$$

*Formalization.* `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorantCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real nodes L and H, this total real expression defines a. Its interpolation and sign properties below assume 0<L<H, so the denominator is strictly positive.

**Definition 1.2 (The tangent interpolant).**

$$\operatorname{P}\left(t\right)=\operatorname{f}\left(L\right)+\operatorname{deriv}\left(f, L\right)(t-L)+a(t-L)^{2}$$

*Formalization.* `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any real L, H, and t, define P(t) by the displayed formula, with a the coefficient above. It is quadratic in t and has derivative f'(L) at L.

**Theorem 1.3 (The strict tangent estimate).**

$$(0<L<H) \implies \operatorname{f}\left(H\right)-\operatorname{f}\left(L\right)<\operatorname{deriv}\left(f, L\right)(H-L)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.logValue_sub_lt_tangent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<L<H. The mean value theorem supplies c strictly between L and H whose derivative equals the secant slope. The first derivative of f strictly decreases on the positive half-line, since its second derivative is negative. Thus the secant slope is strictly less than f'(L); multiplication by H-L gives the estimate.

**Theorem 1.4 (The coefficient is negative).**

$$(0<L<H) \implies a<0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant_coeff_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 0<L<H, the strict tangent estimate makes the numerator negative, and the squared distance in the denominator is positive. Hence a<0.

**Theorem 1.5 (Equality at both nodes).**

$$(L<H) \implies \operatorname{P}\left(L\right)=\operatorname{f}\left(L\right) \land \operatorname{P}\left(H\right)=\operatorname{f}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant_at_nodes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real L<H, substitution gives P(L)=f(L). At H the quadratic coefficient cancels the squared node distance, giving P(H)=f(H). This equality requires only distinct ordered nodes, without a positivity assumption.

**Theorem 1.6 (The majorant on the positive interval).**

$$(0<L<H \land 0<t \le H) \implies \operatorname{f}\left(t\right) \le \operatorname{P}\left(t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.logValue_le_majorant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0<L<H and 0<t<=H. The quadratic has zero third derivative, agrees with f in value and derivative at L, and agrees in value at H. The positive third derivative of f gives the Hermite majorant. The interval includes 0<t<L: the sign to the left of the double node follows from repeated mean value and Rolle arguments on the positive interval spanned by t, L, and H. At L and H equality holds. No bound beyond H is asserted.

**Theorem 1.7 (A quadratic sum from three moments).**

$$\sum_{i \in I}\operatorname{w}\left(i\right) \operatorname{p}\left(\operatorname{x}\left(i\right)\right)=\operatorname{p}\left(m+(K-1)r\right)+(K-1)\operatorname{p}\left(m-r\right)+C(W-V)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_quadratic_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here K, m, r, A, B, C, V, and W are arbitrary real numbers; weights may have either sign. Assume sum w(i)=K, sum w(i)x(i)=Km, sum w(i)(x(i)-m)^2=W, and V=K(K-1)r^2. Set p(t)=A+B(t-(m-r))+C(t-(m-r))^2. Then the displayed identity holds, with no positivity or cardinality requirement.

The centered first moment is zero. Shifting the center from m to m-r gives weighted first moment Kr and weighted second moment W+Kr^2. Expanding p therefore gives KA+BKr+C(W+Kr^2). Evaluating at the prototype nodes m+(K-1)r and m-r, with masses one and K-1, yields the same expression plus C(V-W).

For the remaining statements, k is at least two, m>0, and 0<V<k(k-1)m^2. Set r=sqrt(V/(k(k-1))), L=m-r, and H=m+(k-1)r. These satisfy 0<L<H and V=k(k-1)r^2. The reference envelope is psiK(k,m,V)=f(H)+(k-1)f(L). Assume sum w(i)=k, sum w(i)x(i)=km, and sum w(i)(x(i)-m)^2=W.

**Theorem 1.8 (The exact majorant sum).**

$$\sum_{i \in I}\operatorname{w}\left(i\right) \operatorname{P}\left(\operatorname{x}\left(i\right)\right)=\operatorname{psiK}\left(k, m, V\right)+a(W-V)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_majorant_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the reference domain and three moment equalities, apply the weighted quadratic identity with A=f(L), B=f'(L), and C=a. Interpolation replaces P(H)+(k-1)P(L) by psiK(k,m,V). The exact sum identity permits signed weights and arbitrary real support.

**Theorem 1.9 (The weighted logarithmic bound).**

$$\sum_{i \in I}\operatorname{w}\left(i\right) \operatorname{f}\left(\operatorname{x}\left(i\right)\right) \le \operatorname{psiK}\left(k, m, V\right)+a(W-V)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_majorant_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In addition to the reference domain and moment equalities, assume every weight is nonnegative and every support point satisfies 0<x(i)<=H. Multiplying f(x(i))<=P(x(i)) by w(i), summing, and using the exact majorant sum gives the bound. The weighted variance W is not required to be in the domain of psiK(k,m,W); only the reference variance V appears as an envelope argument.

**Theorem 1.10 (A variance floor removes the correction).**

$$(V \le W) \implies \sum_{i \in I}\operatorname{w}\left(i\right) \operatorname{f}\left(\operatorname{x}\left(i\right)\right) \le \operatorname{psiK}\left(k, m, V\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_le_psiK_of_variance_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under all assumptions of the weighted logarithmic bound, additionally assume V<=W. Since a<0, the correction a(W-V) is nonpositive, so the weighted logarithmic sum is at most psiK(k,m,V). Equality of the variances is allowed.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.logValue_le_majorant`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.logValue_sub_lt_tangent`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorantCoeff`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant_at_nodes`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.majorant_coeff_neg`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_le_psiK_of_variance_ge`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_majorant_bound`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_majorant_sum`
- Truth anchor: `D5/S3/Analytic/Interpolation/QuadraticMajorantEnvelope.weighted_quadratic_sum`
- Dependency: [D5/S3/Analytic/Interpolation/EnvelopeKMonotone](EnvelopeKMonotone.md)
