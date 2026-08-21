# Normalized Motion

## Abstract

Iterated normalized motion stays canonical and decodes to a product of steps.

The clause reads the motion as a state step: an accumulator advances by the control, and the encoding advances by adding the control's code and renormalizing, so motion never produces an illegal encoding.

One step of that already existed, together with its uniqueness and the multiplicativity of its decoder. What did not exist is the iteration: a trajectory of states, and the decoder's behaviour along it. Legality along the trajectory is structural, since the state type carries canonicity as a field; the content is that the decoder turns the whole trajectory into a power.

**Lemma 1.1 (Motion never leaves the canonical encodings).**

$$\operatorname{motion}\left(t + 1\right) = \operatorname{normalize}\left(\operatorname{motion}\left(t\right) + u\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/NormalizedMotion.motion_canonical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every reachable state is a table, and a table is canonical on every axis by construction, so no step can produce adjacent ones, a carry, or a repeated activation.

**Lemma 1.2 (One step multiplies the decoded value).**

$$\operatorname{decode}\left(\operatorname{motion}\left(t + 1\right)\right) = \operatorname{decode}\left(\operatorname{motion}\left(t\right)\right) \cdot \operatorname{decode}\left(u\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/NormalizedMotion.decode_motion_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Addition of codes followed by normalization is multiplication of the decoded values, which is the existing one-step result applied along the trajectory.

**Theorem 1.3 (The trajectory decodes to a power of the control).**

$$\operatorname{decode}\left(\operatorname{motion}\left(t\right)\right) = \operatorname{decode}\left(z\right) \cdot \operatorname{decode}\left(u\right)^{t}$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/NormalizedMotion.decode_motion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Motion in the encoding is multiplication in the value: after any number of steps the decoded state is the initial value times that many copies of the control.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxis/NormalizedMotion.decode_motion`
- Truth anchor: `D5/S1/Digit/PrimeAxis/NormalizedMotion.decode_motion_succ`
- Truth anchor: `D5/S1/Digit/PrimeAxis/NormalizedMotion.motion_canonical`
- Dependency: [D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique](PrimeAxisNormalizationUnique.md)
