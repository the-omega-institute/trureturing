# The Robin budget on an outer power window

## Abstract

Robin window mass and the Riemann hypothesis

Take k(t)=(ψ(t)-t)/t² in the weighted-tail estimate. Write q(x) for the tail of (θ(t)-t)/t², M(Y,B) for the weighted negative mass of k, and E(B) for its endpoint defect. The Robin budget is R(Y,b)=M(Y,Yᵇ)+sqrt(Y) max(-E(Yᵇ),0). The endpoint defect is evaluated at the right endpoint and multiplied by the square root of the left endpoint.

**Theorem 1.1 (Prime mass on the inner power window).**

$$\forall C \in \mathbb{R},\; \forall Y \in \mathbb{R},\; \forall d \in \mathbb{R},\; \forall b \in \mathbb{R},\; \operatorname{exp}\left(1\right) \le Y \Rightarrow \left(1 \le d \Rightarrow \left(d \le b \Rightarrow \left(\left(\forall t \in \mathbb{R},\; 1 \le t \Rightarrow \operatorname{psi}\left(t\right) - \operatorname{theta}\left(t\right) \le C \cdot \operatorname{sqrt}\left(t\right)\right) \Rightarrow \int_{Y}^{Y^{d}} \frac{\operatorname{max}\left(-\operatorname{q}\left(x\right), 0\right)}{\operatorname{sqrt}\left(x\right)} dx \le 4 \cdot Y^{\frac{d - 1}{2}} \cdot \operatorname{R}\left(Y, b\right) + 2 \cdot C \cdot (d - 1) \cdot \operatorname{log}\left(Y\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.prime_mass_le_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correction from ψ to θ costs at most 2C(d-1)log(Y). On the inner window the endpoint length in the square-root variable is at most Y^((d-1)/2)sqrt(Y), and the coefficient of the weighted negative mass is at most 4.

**Theorem 1.2 (A lower bound on every sufficiently late outer window).**

$$\forall z \in \mathbb{C},\; \operatorname{zeta}\left(z\right) = 0 \Rightarrow \left(\frac{1}{2} < \operatorname{Re}\left(z\right) \Rightarrow \left(\operatorname{Re}\left(z\right) < 1 \Rightarrow \left(\forall b \in \mathbb{R},\; \forall e \in \mathbb{R},\; 1 < b \Rightarrow \left(0 < e \Rightarrow \left(\exists T \in \mathbb{R},\; \forall Y \in \mathbb{R},\; T \le Y \Rightarrow Y^{\operatorname{Re}\left(z\right) - \frac{1}{2} - e} \le \operatorname{R}\left(Y, b\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.off_line_zero_forces_robin_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a zero with real part β in (1/2,1), choose one inner exponent d strictly between 1 and b and sufficiently close to 1. The prime-tail lower bound on the inner window has exponent d(β-1/2)-δ. This positive power absorbs the logarithmic correction. After subtracting the transport loss (d-1)/2 and absorbing the fixed factor, the exponent β-1/2-ε remains.

**Theorem 1.3 (Arbitrarily late small Robin windows imply RH).**

$$\forall b \in \mathbb{R},\; 1 < b \Rightarrow \left(\left(\forall e \in \mathbb{R},\; 0 < e \Rightarrow \left(\forall T \in \mathbb{R},\; \exists Y \in \mathbb{R},\; T \le Y \land \operatorname{R}\left(Y, b\right) \le Y^{e}\right)\right) \Rightarrow RiemannHypothesis\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.rh_of_frequently_small_robin_windows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each positive η it suffices to have arbitrarily late windows on which the joint budget is at most Y^η. A right-half-strip zero would contradict this for η=(β-1/2)/3. The right-half-strip reduction then gives the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.off_line_zero_forces_robin_budget`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.prime_mass_le_power`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/RobinWindowMass.rh_of_frequently_small_robin_windows`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeWindowPoleGrowth](PrimeWindowPoleGrowth.md)
- Dependency: [D5/S3/Weil/Mertens/WeightedTailWindowMass](../WeightedTailWindowMass.md)
