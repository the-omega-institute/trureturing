# Rational scalar exponential equations

## Abstract

Scalar exponentials give unique normalized rational solutions of triangular equations and a local valuation bound from the strict prefix.

**Definition 1.1 (Formal scalar exponential).**

$$\forall t: \mathbb{Q}, \forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{expSeries}\left(t, F\right) = \operatorname{subst}\left(\operatorname{C}\left(t\right) \cdot F, \operatorname{exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.expSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The operation is substitution into the formal exponential over Q. The first argument of PowerSeries.subst is the inner series. When the inner series has constant coefficient zero, this is exp(t F).

**Theorem 1.2 (Unique rational normalized triangular source).**

$$\forall lam: \operatorname{Function}\left(\mathbb{N}, \mathbb{Q}\right), \forall mu: \operatorname{Function}\left(\mathbb{N}, \mathbb{Q}\right), (\forall n: \mathbb{N}, (1 \le n) \implies (\neg(lam\left(n\right) = 0))) \implies (\exists F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(F\right) = 0 \land \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(lam\left(n\right), F\right)\right) = mu\left(n\right) \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(lam\left(n\right), F\right)\right))) \land \forall G: \operatorname{PowerSeries}\left(\mathbb{Q}\right), ((\operatorname{constantCoeff}\left(G\right) = 0 \land \forall n: \mathbb{N}, (1 \le n) \implies (\operatorname{coeff}\left(n, \operatorname{expSeries}\left(lam\left(n\right), G\right)\right) = mu\left(n\right) \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(lam\left(n\right), G\right)\right)))) \implies (G = F))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.triangular_exists_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300595 cubic-exponential ordinary series*. URL: <https://oeis.org/A300595>.

*Commentary.*

The functions lam and mu are arbitrary rational-valued functions on the natural numbers, and lam(n) is nonzero for every n>=1. A degree-n change of the exponent changes the degree-n exponential coefficient by lam(n) times that change and preserves all lower coefficients. The derivative recurrence and coefficient agreement give this residual identity. PowerSeriesNormalizedContraction.exists_unique_fixed then constructs the unique normalized solution over Q. The hypotheses concern rational series in arbitrary degree. Taking lam(n)=mu(n)=n^3 gives the rational characterization used by HannaA300595Integrality.

**Theorem 1.3 (Local valuation from the strict prefix).**

$$\forall p: \mathbb{N}, (\operatorname{Prime}\left(p\right)) \implies (\forall t: \mathbb{Q}, (\neg(t = 0)) \implies ((1 \le \operatorname{padicValRat}\left(p, t\right)) \implies (\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(F\right) = 0) \implies (\forall n: \mathbb{N}, (2 \le n) \implies ((\forall j: \mathbb{N}, (j < n) \implies (\operatorname{IsRIntegralRat}\left(p, \operatorname{coeff}\left(j, F\right)\right))) \implies ((\operatorname{coeff}\left(n, \operatorname{expSeries}\left(t, F\right)\right) = t \cdot \operatorname{coeff}\left(n - 1, \operatorname{expSeries}\left(t, F\right)\right)) \implies ((\neg(\operatorname{coeff}\left(n, F\right) = 0)) \implies (\operatorname{padicValRat}\left(p, t\right) - 1 \le \operatorname{padicValRat}\left(p, \operatorname{coeff}\left(n, F\right)\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.local_automatic_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2018). *OEIS A300595 cubic-exponential ordinary series*. URL: <https://oeis.org/A300595>.

*Commentary.*

Truncation before degree n preserves the exponential coefficients below n. If h=v_p(t)>=1, the degree-(n-1) exponential coefficient of the truncated series has valuation at least h when nonzero. The degree-n exponential coefficient of that series has valuation at least 2h-1 when nonzero, since its zeroth and first power contributions vanish. Both estimates use v_p(j!)<=j-1 for positive j. The degree-n residual identity and the given exponential equation express the original coefficient as the difference of the first truncated coefficient and the second divided by t. This yields the displayed lower bound. The cubic integrality proof applies it with t=n^3 at every prime dividing n.

## References

- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.expSeries`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.local_automatic_bound`
- Truth anchor: `D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.triangular_exists_unique`
- Dependency: [D5/S1/Recurrence/Algebraic/DoldExponentialIntegrality](DoldExponentialIntegrality.md)
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../Invariants/PowerSeriesNormalizedContraction.md)
