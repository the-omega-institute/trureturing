# Laguerre-Chebyshev Duality

## Abstract

The Laguerre time observation equals the Chebyshev derivative jet of one budget curve.

**Theorem 1.1 (Laguerre-Chebyshev duality).**

$$\forall nu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), n \in \operatorname{Nat}\left(\right), u \in \operatorname{Real}\left(\right), p \in \operatorname{Fin}\left(n + 1\right) \to \operatorname{Real}\left(\right),\; \left(\operatorname{map}\left(\operatorname{lambda}\left(xi, \operatorname{neg}\left(xi\right)\right), nu\right) = nu \land \left(1 \le n \land \left(0 < u \land \left(\left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{ChebyshevT}\left(\operatorname{Int}\left(\right), n, 1 - 2 \cdot x\right) = \operatorname{sum}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{lambda}\left(k, p\left(k\right) \cdot \operatorname{pow}\left(x, k\right)\right)\right)\right) \land \operatorname{Integrable}\left(\operatorname{lambda}\left(xi, \frac{1}{\operatorname{pow}\left(xi, 2\right) + u}\right), nu\right)\right)\right)\right)\right) \Rightarrow let scale: \operatorname{Real}\left(\right) = \operatorname{sqrt}\left(u\right); let weighted: \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right) = \operatorname{resolventWeightedMeasure}\left(nu, scale\right); let budget: \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right) = \operatorname{lambda}\left(v, \operatorname{integral}\left(nu, \operatorname{lambda}\left(xi, \frac{1}{\operatorname{pow}\left(xi, 2\right) + v}\right)\right)\right); \operatorname{complex}\left(budget\left(u\right)\right) - \operatorname{complex}\left(2 \cdot scale\right) \cdot \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{exp}\left(\operatorname{neg}\left(scale \cdot t\right)\right) \cdot \operatorname{laguerreOne}\left(n - 1, 2 \cdot scale \cdot t\right)\right) \cdot \operatorname{resolventCorrelation}\left(weighted, t\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right) = \operatorname{complex}\left(\operatorname{sum}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{lambda}\left(k, p\left(k\right) \cdot \operatorname{pow}\left(u, k\right) \cdot \frac{\operatorname{pow}\left(\operatorname{neg}\left(1\right), k\right)}{\operatorname{factorial}\left(k\right)} \cdot \operatorname{iteratedDeriv}\left(k, budget, u\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality.laguerre_chebyshev_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive square scale constructs the canonical resolvent-weighted measure. The imported time tomography and scale-jet identities then identify the displayed Laguerre observation and Chebyshev derivative sum.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality.laguerre_chebyshev_duality`
- Dependency: [D5/S3/Weil/Budget/PositiveCayleyScaleTransport](../Budget/PositiveCayleyScaleTransport.md)
- Dependency: [D5/S3/Weil/CayleyLaguerre/CayleyMomentTransport](CayleyMomentTransport.md)
- Dependency: [D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography](../TestFunctions/CayleyLaguerreMomentTomography.md)
