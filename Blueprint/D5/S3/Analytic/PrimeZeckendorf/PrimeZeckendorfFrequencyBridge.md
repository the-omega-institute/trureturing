# Prime-Zeckendorf Frequency Bridge

## Abstract

Zeckendorf long-short layer steps become logarithmically prime-scaled frequency gaps in the golden heat spectrum.

**Theorem 1.1 (Zeckendorf selects the prime-local frequency gap).**

$$\begin{gathered}\forall p: Nat.Primes, v\in\mathbb{N},\\{}(\neg(2 \in \operatorname{wdigits}(v)) \Rightarrow \operatorname{primeLayerFrequency}(p, v+1) - \operatorname{primeLayerFrequency}(p, v) = \varphi^{2} \times \log(p)) \land\\{}(2 \in \operatorname{wdigits}(v) \Rightarrow \operatorname{primeLayerFrequency}(p, v+1) - \operatorname{primeLayerFrequency}(p, v) = \varphi \times \log(p)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyBridge.zeckendorf_selects_prime_frequency_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Within a fixed prime channel, absence of Fibonacci index two selects the long phi-squared times log p increment, while presence selects the short phi times log p increment.

The theorem composes the existing Zeckendorf beta-gap bridge with the separable golden heat energy beta(v) log p. Frequency here is an analytic heat-energy coordinate, not a claim that a projection layer is itself one physical frequency.

**Theorem 1.2 (Prime channels share one golden symbolic increment).**

$$\begin{gathered}\forall p, q: Nat.Primes, v\in\mathbb{N},\\{}\log(q) \times (\operatorname{primeLayerFrequency}(p, v+1) - \operatorname{primeLayerFrequency}(p, v)) = \log(p) \times (\operatorname{primeLayerFrequency}(q, v+1) - \operatorname{primeLayerFrequency}(q, v)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyBridge.cross_prime_frequency_gap_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After cross-multiplication by the logarithmic prime coordinates, consecutive frequency gaps agree across any two prime channels.

This proves separability of prime scale and golden depth. It supplies no canonical geometric identification of the prime labels, which remains blocked by prime-relabeling symmetry.

## References

- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyBridge.cross_prime_frequency_gap_balance`
- Truth anchor: `D5/S3/Analytic/PrimeZeckendorf/PrimeZeckendorfFrequencyBridge.zeckendorf_selects_prime_frequency_gap`
- Dependency: [D5/S3/Analytic/PrimeZeckendorf/ZeckendorfGoldenBetaGapBridge](ZeckendorfGoldenBetaGapBridge.md)
- Dependency: [D5/S3/Midline/GoldenHeatSpectrum](../../Midline/GoldenHeatSpectrum.md)
