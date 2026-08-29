# Approximate Complementary Concentration

## Abstract

Residual spectral energy controls the mass away from Fourier near-zeros.

**Theorem 1.1 (Residual spectral mass concentrates near Fourier zeros).**

$$\begin{aligned}\forall mu: \operatorname{Measure}(\mathbb{R}), F: \mathbb{R} \to \mathbb{C},\\epsilon: \operatorname{ENNReal}(), delta: NNReal,\\\operatorname{AEMeasurable}(F, mu) \land 0 < delta \land \operatorname{lintegral}(mu, (xi: \mathbb{R} \mapsto \operatorname{enorm}(\operatorname{apply}(F, xi))^{2})) = epsilon \Rightarrow\\\operatorname{measure}(mu, \left\{\operatorname{toENNReal}(delta) \leq \operatorname{enorm}(\operatorname{apply}(F, xi)) \mid xi \in \mathbb{R}\right\}) \leq \frac{epsilon}{\operatorname{toENNReal}(delta)^{2}}.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Budget/ApproximateComplementaryConcentration.approximate_complementary_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a positive Borel measure carry the residual spectrum and let a measurable complex function be the Fourier transform of the window test.

If its squared modulus has residual energy epsilon, Markov's inequality bounds the mass where the modulus exceeds a positive finite threshold delta by epsilon divided by delta squared.

## References

- Truth anchor: `D5/S3/Weil/Budget/ApproximateComplementaryConcentration.approximate_complementary_concentration`
