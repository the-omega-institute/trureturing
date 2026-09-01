# Single-Defect Horizon Thermodynamic Asymptotics

## Abstract

The squeezing coordinate, occupation number, and free energy of a positive single-defect depth have exact horizon identities and first-order boundary asymptotics.

**Theorem 1.1 (The horizon corrections have universal leading coefficients).**

$$\forall delta \in \mathbb{R}_{\geq0}, delta \neq 0 \Rightarrow ((\forall omega, \operatorname{D}(delta, omega) = \frac{delta^2-omega^2}{delta^2}) \land (\forall omega, \lvert omega \rvert < delta \Rightarrow \operatorname{F}(delta, omega) = 2\operatorname{log}(\operatorname{cosh}(\operatorname{r}(delta, omega))) = \operatorname{log}(1+\operatorname{N}(delta, omega))) \land \lim_{epsilon\to 0^{+}} \frac{\operatorname{r}(delta, delta-epsilon)-\frac{1}{2} \operatorname{log}(\frac{2delta}{epsilon})}{epsilon} = -\frac{1}{4delta} \land \lim_{epsilon\to 0^{+}} \operatorname{N}(delta, delta-epsilon)-\frac{delta}{2epsilon} = -\frac{3}{4} \land \lim_{epsilon\to 0^{+}} \frac{\operatorname{F}(delta, delta-epsilon)-\operatorname{log}(\frac{delta}{2epsilon})}{epsilon} = \frac{1}{2delta} \land \lim_{omega\to delta^{-}} \operatorname{F}(delta, omega) = \infty).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaLinear/HorizonThermodynamicAsymptotics.single_defect_horizon_thermodynamic_asymptotics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonzero nonnegative depth delta, the existing horizon determinant law is retained. In the strict interior, the negative-log free energy equals both twice log cosh of the artanh squeezing coordinate and log of one plus occupation.

Writing epsilon=delta-omega and approaching zero from above, the three normalized errors converge respectively to -1/(4 delta), -3/4, and 1/(2 delta). These exact limits strengthen the source's two O(epsilon) and one O(1) claims.

The Lean module computes the interior point delta=2, omega=1 and the excluded zero-depth case exactly, preventing totalized division or logarithms from making the theorem vacuous.

## References

- Truth anchor: `D5/S3/Weil/ZetaLinear/HorizonThermodynamicAsymptotics.single_defect_horizon_thermodynamic_asymptotics`
- Dependency: [D5/S3/Weil/ZetaLinear/HorizonFreeEnergyDivergence](HorizonFreeEnergyDivergence.md)
