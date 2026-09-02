# Compactified Squared-Distance Support

## Abstract

A rational compactification separates nonnegative and negative squared distances and characterizes critical-line support.

**Theorem 1.1 (Compactified squared-distance support criterion).**

$$\forall a \in \operatorname{Real}\left(\right), x \in \operatorname{Real}\left(\right), delta \in \operatorname{Real}\left(\right),\; \left(\frac{1}{4} < a \land \left(0 \le x \land \left(0 < \operatorname{abs}\left(delta\right) \land delta^{2} < \frac{1}{4}\right)\right)\right) \Rightarrow \operatorname{let} compactCoordinate = (y \mapsto \frac{y - a}{y + a}), \left(-1 \le compactCoordinate\left(x\right) \land compactCoordinate\left(x\right) < 1\right) \land \left(\left(compactCoordinate\left(-delta^{2}\right) = -\frac{a + delta^{2}}{a - delta^{2}} \land compactCoordinate\left(-delta^{2}\right) < -1\right) \land \left(\operatorname{RiemannHypothesis}\left(\right) \Leftrightarrow \left(\forall rho \in \operatorname{Complex}\left(\right),\; \left(\operatorname{riemannZeta}\left(rho\right) = 0 \land \left(\left(\neg \left(\exists n \in \operatorname{Nat}\left(\right),\; rho = -2 \cdot \left(n + 1\right)\right)\right) \land rho \ne 1\right)\right) \Rightarrow \operatorname{let} signedSquaredDistance = -\left(\operatorname{re}\left(rho\right) - \frac{1}{2}\right)^{2}, signedSquaredDistance + a \ne 0 \land compactCoordinate\left(signedSquaredDistance\right) \in \operatorname{Icc}\left(-1, 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/CayleyLaguerre/CompactifiedSquaredDistanceSupport.compactified_squared_distance_support_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compact coordinate is the source rational map, constructed from the supplied scale. Nonnegative inputs land in the unit interval, while a genuine signed squared distance in the critical strip lands strictly below negative one.

For every Mathlib-nontrivial zeta zero, the observed signed squared distance is constructed from its real coordinate. Requiring the rational coordinate to be defined and supported in the closed unit interval is equivalent to the stated critical-line hypothesis.

## References

- Truth anchor: `D5/S3/Weil/CayleyLaguerre/CompactifiedSquaredDistanceSupport.compactified_squared_distance_support_criterion`
- Dependency: [D5/S3/Weil/CayleyLaguerre/ChebyshevSignedDistanceSeparator](ChebyshevSignedDistanceSeparator.md)
