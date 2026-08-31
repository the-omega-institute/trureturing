# Prime-Frequency Fourier Phase Flow

## Abstract

Fourier characters create unitary log-frequency time flow while scalar products forget order.

**Theorem 1.1 (Time-frequency character laws).**

$$\forall frequency \in \mathbb{R}, other \in \mathbb{R}, time \in \mathbb{R}, shift \in \mathbb{R},\; (\operatorname{fourierPhase}\left(frequency, 0\right) = 1 \land\\{}\operatorname{fourierPhase}\left(frequency, time + shift\right) = \operatorname{fourierPhase}\left(frequency, time\right) \cdot \operatorname{fourierPhase}\left(frequency, shift\right) \land\\{}\operatorname{fourierPhase}\left(frequency + other, time\right) = \operatorname{fourierPhase}\left(frequency, time\right) \cdot \operatorname{fourierPhase}\left(other, time\right) \land\\{}\left\lVert \operatorname{fourierPhase}\left(frequency, time\right) \right\rVert = 1 \land\\{}\operatorname{fourierPhase}\left(frequency, time\right) = \operatorname{fourierPhase}\left(time, frequency\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.fourier_phase_character_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real frequency, comparison frequency, time, and shift, the phase at zero time is one, addition in either real argument becomes multiplication, and the phase has norm one.

The final equality records symmetry of the numerical bilinear pairing between time and frequency. It does not identify their semantic roles or assert a preferred time direction.

**Theorem 1.2 (Scalar phase products forget order).**

$$\forall frequencies \in \operatorname{List}\left(\mathbb{R}\right), time \in \mathbb{R},\; \operatorname{orderedPhaseProduct}\left(frequencies, time\right) = \operatorname{fourierPhase}\left(\operatorname{sum}\left(frequencies\right), time\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.ordered_phase_product_collapse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite list of real frequencies and every real time, the listed scalar phase product is the single phase at the sum of those frequencies.

Consequently, lists with the same sum are indistinguishable at this commutative scalar-product layer. This is a countermodel to recovering list order from that product alone, not a claim that all Fourier or memory-bearing observer models erase chronology.

**Theorem 1.3 (Finite synthesis shift and norm laws).**

$$\forall iota \in \operatorname{Type}, fintypeWitness \in \operatorname{Fintype}\left(iota\right), amplitude \in iota \to \mathbb{C}, frequency \in iota \to \mathbb{R}, time \in \mathbb{R}, shift \in \mathbb{R},\; (\operatorname{finiteFourierSynthesis}\left(amplitude, frequency, time + shift\right) = \sum_{p: iota} amplitude\left(p\right) \cdot \operatorname{fourierPhase}\left(frequency\left(p\right), time\right) \cdot \operatorname{fourierPhase}\left(frequency\left(p\right), shift\right) \land\\{}\left\lVert \operatorname{finiteFourierSynthesis}\left(amplitude, frequency, time\right) \right\rVert \le \sum_{p: iota} \left\lVert amplitude\left(p\right) \right\rVert)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.finite_fourier_synthesis_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite index type, complex amplitudes, real frequencies, and real time and shift, translating time distributes the shift phase through every term of the finite synthesis.

At the original time, the synthesis norm is at most the sum of the amplitude norms because each phase has norm one. The theorem does not assert equality, inversion, Plancherel, irreversibility, or any statement about zero locations.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.finite_fourier_synthesis_laws`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.fourier_phase_character_laws`
- Truth anchor: `D5/S3/Observer/AgencyHolonomy/PrimeFrequencyPhaseFlow.ordered_phase_product_collapse`
- Dependency: [D5/S3/Observer/AgencyHolonomy/FiniteHolonomyEnergy](FiniteHolonomyEnergy.md)
