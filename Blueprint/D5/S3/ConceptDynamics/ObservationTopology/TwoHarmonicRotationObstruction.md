# Two-Harmonic Rotation Obstruction

## Abstract

Coprime frequency pairs meet a sharp half-cosine barrier at angle pi/6.

**Theorem 1.1 (Coprime frequency pairs cannot both avoid the half-cosine barrier).**

$$\forall m \in \mathbb{N}, n \in \mathbb{N},\; \operatorname{Coprime}\left(m, n\right) \Rightarrow \frac{1}{2} \le \operatorname{max}\left(\left|\operatorname{cos}\left(\operatorname{real}\left(m\right) \cdot \frac{\pi}{6}\right)\right|, \left|\operatorname{cos}\left(\operatorname{real}\left(n\right) \cdot \frac{\pi}{6}\right)\right|\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ObservationTopology/TwoHarmonicRotationObstruction.coprime_two_frequency_cosine_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing a frequency modulo six lists every possible cosine magnitude at a rotation angle of pi over six. A magnitude strictly below one half forces residue three.

If both frequencies had magnitude below one half, both would be divisible by three. That common divisor contradicts their coprimality, so at least one magnitude reaches the barrier.

The discrete frequency obstruction applies to the stable-rank measurement-design question of Eftekhari et al. (2018), recorded in Library/ConceptDynamics/eftekhari2018embedology.md, when the sensor class is restricted to paired circle harmonics at a pi/6 delay. It does not by itself assert the analytic stable-rank formula or a dimension bound for arbitrary smooth sensors.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ObservationTopology/TwoHarmonicRotationObstruction.coprime_two_frequency_cosine_obstruction`
