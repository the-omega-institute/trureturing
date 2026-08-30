# Laguerre-Chebyshev Duality

## Abstract

The Laguerre time observation equals the Chebyshev derivative jet of one budget curve.

**Theorem 1.1 (Laguerre-Chebyshev duality).**

$$\forall nu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), n \in \operatorname{Nat}\left(\right), u \in \operatorname{Real}\left(\right), p \in \operatorname{Fin}\left(n + 1\right) \to \operatorname{Real}\left(\right),\; \left(\operatorname{map}\left(\operatorname{lambda}\left(xi, \operatorname{neg}\left(xi\right)\right), nu\right) = nu \land \left(1 \le n \land \left(0 < u \land \left(\left(\forall x \in \operatorname{Real}\left(\right),\; \operatorname{ChebyshevT}\left(\operatorname{Int}\left(\right), n, 1 - 2 \cdot x\right) = \operatorname{sum}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{lambda}\left(k, p\left(k\right) \cdot \operatorname{pow}\left(x, k\right)\right)\right)\right) \land \operatorname{Integrable}\left(\operatorname{lambda}\left(xi, \frac{1}{\operatorname{pow}\left(xi, 2\right) + u}\right), nu\right)\right)\right)\right)\right) \Rightarrow let scale: \operatorname{Real}\left(\right) = \operatorname{sqrt}\left(u\right); let laguerreOne: \operatorname{Nat}\left(\right) \to \left(\operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right)\right) = \operatorname{lambda}\left(m, \operatorname{lambda}\left(x, \operatorname{sum}\left(\operatorname{range}\left(m + 1\right), \operatorname{lambda}\left(j, \frac{\operatorname{pow}\left(\operatorname{neg}\left(1\right), j\right) \cdot \operatorname{choose}\left(m + 1, j + 1\right)}{\operatorname{factorial}\left(j\right)} \cdot \operatorname{pow}\left(x, j\right)\right)\right)\right)\right); let weighted: \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right) = \operatorname{withDensity}\left(nu, \operatorname{lambda}\left(xi, \operatorname{ofReal}\left(\operatorname{inv}\left(\operatorname{pow}\left(xi, 2\right) + \operatorname{pow}\left(scale, 2\right)\right)\right)\right)\right); let correlation: \operatorname{Real}\left(\right) \to \operatorname{Complex}\left(\right) = \operatorname{lambda}\left(t, \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \operatorname{exp}\left(\operatorname{I}\left(\right) \cdot t \cdot xi\right), weighted\right)\right); let budget: \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right) = \operatorname{lambda}\left(v, \operatorname{integral}\left(nu, \operatorname{lambda}\left(xi, \frac{1}{\operatorname{pow}\left(xi, 2\right) + v}\right)\right)\right); \operatorname{complex}\left(budget\left(u\right)\right) - \operatorname{complex}\left(2 \cdot scale\right) \cdot \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{exp}\left(\operatorname{neg}\left(scale \cdot t\right)\right) \cdot laguerreOne\left(n - 1, 2 \cdot scale \cdot t\right)\right) \cdot correlation\left(t\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right) = \operatorname{complex}\left(\operatorname{sum}\left(\operatorname{Fin}\left(n + 1\right), \operatorname{lambda}\left(k, p\left(k\right) \cdot \operatorname{pow}\left(u, k\right) \cdot \frac{\operatorname{pow}\left(\operatorname{neg}\left(1\right), k\right)}{\operatorname{factorial}\left(k\right)} \cdot \operatorname{iteratedDeriv}\left(k, budget, u\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality.laguerre_chebyshev_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The positive square scale constructs the resolvent-weighted measure. Finite-sum Laplace integration proves the time observation directly, and the scale-jet identity identifies its Cayley moment with the derivative sum.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/LaguerreChebyshevDuality.laguerre_chebyshev_duality`
- Dependency: [D5/S3/Weil/CayleyLaguerre/CayleyMomentTransport](CayleyMomentTransport.md)
- Dependency: [D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography](../TestFunctions/CayleyLaguerreMomentTomography.md)
