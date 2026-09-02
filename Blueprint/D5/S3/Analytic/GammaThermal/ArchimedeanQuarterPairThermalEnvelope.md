# Archimedean Quarter-Pair Thermal Envelope

## Abstract

The two quarter-shifted Archimedean Gamma channels have an exact thermal envelope.

**Theorem 1.1 (The quarter-pair Gamma product has a Fermi-like thermal envelope).**

$$\forall t \in \operatorname{Real}\left(\right),\; (\left|\operatorname{Gamma}\left(\frac{1}{4} + i \times \frac{t}{2}\right)\right|)^{2} \times (\left|\operatorname{Gamma}\left(\frac{3}{4} + i \times \frac{t}{2}\right)\right|)^{2} = \frac{2 \times (\pi)^{2}}{\operatorname{cosh}\left(\pi \times t\right)} \land \frac{1}{\operatorname{cosh}\left(\pi \times t\right)} = \frac{2 \times \operatorname{exp}\left(-\pi \times \left|t\right|\right)}{1 + \operatorname{exp}\left(-2 \times \pi \times \left|t\right|\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/GammaThermal/ArchimedeanQuarterPairThermalEnvelope.archimedean_quarter_pair_thermal_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t, the first conjunct gives the squared-norm product of Gamma(1/4 + it/2) and Gamma(3/4 + it/2) as 2 pi^2 / cosh(pi t). The second conjunct gives exactly the reciprocal-cosh exponential identity with |t|.

The proof specializes the pinned Gamma duplication and reflection identities, then rewrites the hyperbolic cosine using real exponentials. It uses no Riemann-hypothesis assumption.

## References

- Truth anchor: `D5/S3/Analytic/GammaThermal/ArchimedeanQuarterPairThermalEnvelope.archimedean_quarter_pair_thermal_envelope`
