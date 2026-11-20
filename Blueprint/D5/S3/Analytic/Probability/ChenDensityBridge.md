# Density tilts and exact inclusion probabilities

## Abstract

Real density tilts on fixed-size samples preserve inclusion events up to the matched moment order.

**Theorem 1.1 (Lifting a real density to the same finite sample space).**

$$\begin{aligned}\forall m,r:\mathbb{N}, \forall g: \mathbb{R} \to \mathbb{R}, \operatorname{Measurable}\left(g\right) \Rightarrow\\(\forall x: \mathbb{R}, 0 \leq \operatorname{g}\left(x\right)) \Rightarrow\int \operatorname{g}\left(x\right) d\mu=1 \Rightarrow\\(\forall i: \mathbb{N}, 0 < i \leq r \Rightarrow\int x^{i}(\operatorname{g}\left(x\right)-1) d\mu=0) \Rightarrow\\\operatorname{map}\left(X, Q\right)=\operatorname{withDensity}\left(\mu, \operatorname{ofReal} \circ g\right) \land\\(\forall A: \operatorname{Finset}\left(\operatorname{Population}\left(m\right)\right), \operatorname{card}\left(A\right) \leq r \Rightarrow \operatorname{Q}\left(\operatorname{inclusion}\left(A\right)\right)=\operatorname{P}\left(\operatorname{inclusion}\left(A\right)\right))\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For stage m, P is uniform on Sample m, X is the common estimator, and the real law mu is map(X,P). The law Q on Sample m has density ofReal(g(X(S))) at a sample S relative to P. Normalization against mu makes Q a probability measure.

Integrating on a real event under the pushforward of Q gives the same integral as tilting mu by g. For a prescribed subset A, the finite sampling identity converts the restricted integral of g(X)-1 into the integral of the centered density against an inclusion polynomial of degree at most card(A). The constant coefficient is controlled by normalization and the other coefficients by the centered moment equations. The resulting equality of event masses holds in ENNReal.

## References

- Truth anchor: `D5/S3/Analytic/Probability/ChenDensityBridge.tiltedSample_spec`
