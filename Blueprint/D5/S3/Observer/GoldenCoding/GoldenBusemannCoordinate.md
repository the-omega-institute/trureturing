# Golden Busemann Coordinate

## Abstract

Golden null coefficients carry a nontrivial Busemann rapidity coordinate.

**Theorem 1.1 (The golden null basis exposes Busemann rapidity).**

$$let Q_{\phi}(x, y) = x^{2} - x \cdot y - y^{2}; let v(a, b) = \operatorname{pair}\left(a \cdot \phi + b \cdot phiPrime, a + b\right); let eta(a, b) = \frac{1}{2} \cdot \operatorname{log}\left(\frac{a}{-b}\right); let beta_{1}(a, b, c, d) = eta\left(c, d\right) - eta\left(a, b\right); \left(\left(\left(\left(\left(\left(\left(Q_{\phi}\right)\left(\phi, 1\right) = 0 \land \left(Q_{\phi}\right)\left(phiPrime, 1\right) = 0\right) \land \left(\forall a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right),\; \left(Q_{\phi}\right)\left(\operatorname{pair}\left(a \cdot \phi + b \cdot phiPrime, a + b\right)\right) = -5 \cdot a \cdot b\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right),\; \left(0 < a \land b < 0\right) \Rightarrow 0 < \frac{a}{-b}\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right),\; \left(\left(0 < a \land b < 0\right) \land \left(Q_{\phi}\right)\left(\operatorname{pair}\left(a \cdot \phi + b \cdot phiPrime, a + b\right)\right) = 1\right) \Rightarrow eta\left(a, b\right) = \operatorname{log}\left(a \cdot \operatorname{sqrt}\left(5\right)\right)\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right), c \in \operatorname{Real}\left(\right), d \in \operatorname{Real}\left(\right), e \in \operatorname{Real}\left(\right), f \in \operatorname{Real}\left(\right),\; \left(beta_{1}\right)\left(a, b, c, d\right) + \left(beta_{1}\right)\left(c, d, e, f\right) = \left(beta_{1}\right)\left(a, b, e, f\right)\right)\right) \land \left(\forall a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right),\; \left(0 < a \land b < 0\right) \Rightarrow eta\left(\phi^{2} \cdot a, \phi^{-2} \cdot b\right) = eta\left(a, b\right) + 2 \cdot \operatorname{log}\left(\phi\right)\right)\right) \land \left(\left(\left(\left(\left(Q_{\phi}\right)\left(\operatorname{pair}\left(\frac{1}{\operatorname{sqrt}\left(5\right)} \cdot \phi + -\frac{1}{\operatorname{sqrt}\left(5\right)} \cdot phiPrime, \frac{1}{\operatorname{sqrt}\left(5\right)} + -\frac{1}{\operatorname{sqrt}\left(5\right)}\right)\right) = 1 \land eta\left(\frac{1}{\operatorname{sqrt}\left(5\right)}, -\frac{1}{\operatorname{sqrt}\left(5\right)}\right) = 0\right) \land \left(Q_{\phi}\right)\left(\operatorname{pair}\left(\frac{2}{\operatorname{sqrt}\left(5\right)} \cdot \phi + -\frac{1}{2 \cdot \operatorname{sqrt}\left(5\right)} \cdot phiPrime, \frac{2}{\operatorname{sqrt}\left(5\right)} + -\frac{1}{2 \cdot \operatorname{sqrt}\left(5\right)}\right)\right) = 1\right) \land eta\left(\frac{2}{\operatorname{sqrt}\left(5\right)}, -\frac{1}{2 \cdot \operatorname{sqrt}\left(5\right)}\right) = \operatorname{log}\left(2\right)\right) \land \left(\neg eta\left(\frac{1}{\operatorname{sqrt}\left(5\right)}, -\frac{1}{\operatorname{sqrt}\left(5\right)}\right) = eta\left(\frac{2}{\operatorname{sqrt}\left(5\right)}, -\frac{1}{2 \cdot \operatorname{sqrt}\left(5\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenCoding/GoldenBusemannCoordinate.golden_busemann_coordinate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real Lorentz form uses the existing sign convention Q_phi(x,y)=x^2-xy-y^2. The golden ratio and its negative conjugate give two null vectors, and direct polarization reduces the form of a v_plus+b v_minus to -5ab.

On the branch a>0 and b<0, the ratio a/(-b) is positive. At unit Lorentz level the coefficient product is a(-b)=1/5, so the half-log definition agrees exactly with log(a sqrt(5)). Differences of this coordinate satisfy the Busemann cocycle law by telescoping.

Reciprocal golden-square scaling preserves the branch and adds 2 log(phi) to rapidity. The points with coefficients (1/sqrt(5),-1/sqrt(5)) and (2/sqrt(5),-1/(2sqrt(5))) both have Lorentz value one, but their rapidities are zero and log(2).

## References

- Truth anchor: `D5/S3/Observer/GoldenCoding/GoldenBusemannCoordinate.golden_busemann_coordinate`
- Dependency: [D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix](../../CompletionDynamics/GoldenMobius/GoldenScaleHelix.md)
- Dependency: [D5/S3/Observer/GoldenCoding/GoldenLorentzUpdate](GoldenLorentzUpdate.md)
