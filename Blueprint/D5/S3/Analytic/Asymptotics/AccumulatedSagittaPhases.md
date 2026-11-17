# Accumulated versine of equal angle steps

## Abstract

For every N the accumulated versine of N equal angle steps sigma (T/N)^alpha lies between two explicit polynomials in the step angle. For T > 0 it tends to 0 if alpha > 1/2, to sigma^2 T/2 if alpha = 1/2, and to plus infinity if 0 < alpha < 1/2 and sigma is nonzero; no claim is made for alpha <= 0.

Fix real numbers sigma, T and alpha. For a natural number N the step angle is theta_N = sigma (T/N)^alpha, a real power of the real quotient T/N, and the accumulated versine is A_N = N (1 - cos theta_N). In Lean, division by N = 0 returns 0 and real powers follow the Mathlib conventions; the value A_0 is 0. The versine 1 - cos theta is the sagitta of a unit-circle arc of half-angle theta, which is why the Lean declarations are named after the sagitta.

**Theorem 1.1 (Two-sided bounds for every N).**

$$\theta_{N} = \sigma (T/N)^{\alpha},\quad A_{N} = N (1 - \operatorname{cos} \theta_{N}),\quad\\N (\frac{\theta_{N}^{2}}{2} - \frac{\theta_{N}^{4}}{24}) \le A_{N} \le N \frac{\theta_{N}^{2}}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/AccumulatedSagittaPhases.accumulated_sagitta_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all real sigma, T, alpha and every natural N, the accumulated versine A_N is at least N (theta_N^2/2 - theta_N^4/24) and at most N theta_N^2/2. No sign or size condition on the parameters is assumed.

The upper bound is the Mathlib inequality 1 - x^2/2 <= cos x. For the lower bound write 1 - cos x = 2 sin^2(x/2) and use the Mathlib bound |y - sin y| <= |y|^3/6 at y = x/2: expanding sin^2 y = (y - (y - sin y))^2 and discarding the square of the difference gives sin^2 y >= y^2 - y^4/3, hence 1 - cos x >= x^2/2 - x^4/24 for every real x. Both pointwise bounds are classical Taylor-remainder estimates for the cosine; the lower one is derived here because the pinned Mathlib states the quartic estimate only for |x| <= 1 and with the constant 5/96.

The lower bound is informative only while theta_N^2 < 12; for larger step angles it is negative and says less than A_N >= 0.

**Theorem 1.2 (The three limit regimes).**

$$\theta_{N} = \sigma (T/N)^{\alpha},\quad A_{N} = N (1 - \operatorname{cos} \theta_{N}),\quad\\(T > 0 \land \alpha > \frac{1}{2}) \implies \lim_{N \to \infty} A_{N} = 0,\quad\\(T > 0 \land \alpha = \frac{1}{2}) \implies \lim_{N \to \infty} A_{N} = \frac{\sigma^{2} T}{2},\quad\\(T > 0 \land \sigma \neq 0 \land 0 < \alpha < \frac{1}{2}) \implies \lim_{N \to \infty} A_{N} = \infty.$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Asymptotics/AccumulatedSagittaPhases.accumulated_sagitta_phases` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem assumes 0 < T and all real sigma and alpha. Its first conjunct says that A_N tends to 0 when alpha > 1/2. The second says that A_N tends to sigma^2 T/2 when alpha = 1/2. The third says that A_N tends to plus infinity when sigma is nonzero and 0 < alpha < 1/2.

For positive N one has N theta_N^2 = c N^(1 - 2 alpha) and theta_N^2 = c N^(-2 alpha) with c = sigma^2 T^(2 alpha). When alpha > 1/2 the upper bound tends to 0 and A_N is nonnegative. When alpha = 1/2 the upper bound is the constant sigma^2 T/2 and the lower bound is sigma^2 T/2 - (sigma^2 T)^2/(24 N). When 0 < alpha < 1/2 the step angle squared tends to 0, so it is eventually at most 6 and the lower bound is then at least c N^(1 - 2 alpha)/4, which tends to infinity because c is positive for nonzero sigma.

The divergence conjunct is restricted to alpha > 0. The restriction cannot simply be dropped: at alpha = 0 the step angle is the constant sigma and A_N = N (1 - cos sigma), which vanishes for every N when sigma is a multiple of 2 pi. That observation is a remark and is not formalised. The theorem makes no claim for alpha <= 0, gives no rate in the divergent case, and does not concern unequal steps or random signs.

## References

- Truth anchor: `D5/S3/Analytic/Asymptotics/AccumulatedSagittaPhases.accumulated_sagitta_bounds`
- Truth anchor: `D5/S3/Analytic/Asymptotics/AccumulatedSagittaPhases.accumulated_sagitta_phases`
