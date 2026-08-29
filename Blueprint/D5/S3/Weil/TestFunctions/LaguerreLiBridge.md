# Laguerre-Li Bridge

## Abstract

The natural half-scale Cayley moments give the Laguerre formula for Li curvature.

**Theorem 1.1 (Laguerre-Li bridge).**

$$\forall rho \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), liCoefficient \in \operatorname{Natural}\left(\right) \to \operatorname{Real}\left(\right),\; \left(\left(\left(\operatorname{IsFiniteMeasure}\left(rho\right) \land \operatorname{map}\left(\operatorname{lambda}\left(xi, \operatorname{neg}\left(xi\right)\right), rho\right) = rho\right) \land \operatorname{spectralMass}\left(rho\right) = 2 \cdot liCoefficient\left(1\right)\right) \land \left(\forall k \in \operatorname{Natural}\left(\right),\; 1 \le k \Rightarrow \operatorname{realPart}\left(\operatorname{cayleyMoment}\left(rho, k, \frac{1}{2}\right)\right) = liCoefficient\left(k + 1\right) - 2 \cdot liCoefficient\left(k\right) + liCoefficient\left(k - 1\right)\right)\right) \Rightarrow \left(\forall n \in \operatorname{Natural}\left(\right),\; 1 \le n \Rightarrow liCoefficient\left(n + 1\right) - 2 \cdot liCoefficient\left(n\right) + liCoefficient\left(n - 1\right) = 2 \cdot liCoefficient\left(1\right) - \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{exp}\left(\operatorname{neg}\left(\frac{t}{2}\right)\right) \cdot \operatorname{laguerreOne}\left(n - 1, t\right) \cdot \operatorname{realPart}\left(\operatorname{resolventCorrelation}\left(rho, t\right)\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/LaguerreLiBridge.laguerre_li_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite even real-line spectral measure, assume the natural half-scale Cayley moments are the discrete curvatures of the supplied Li sequence and the total mass is twice its first coefficient. Specializing the canonical Cayley-Laguerre tomography identity gives the displayed real resolvent-correlation integral.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/LaguerreLiBridge.laguerre_li_bridge`
- Dependency: [D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography](CayleyLaguerreMomentTomography.md)
