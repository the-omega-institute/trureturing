# Signed Zeckendorf Orbit Code

## Abstract

The three zero symmetries act on a signed W code by flipping its two sign coordinates.

**Theorem 1.1 (Klein actions are the two independent sign flips).**

$$\begin{aligned}\forall delta, gamma: \mathbb{R}, N, multiplicity: \mathbb{N},\\{}let rho: \mathbb{C} = \frac{1}{2} + delta + \operatorname{ComplexI}\left(\right) \times gamma;\\{}let unsignedThread: \mathbb{R} \to WDigitString = (x \mapsto \operatorname{wEncoding}\left(\left\lfloor\varphi^{{N}} \cdot \left\lVert x \right\rVert\right\rfloor\right));\\{}let code: \mathbb{C} \to {SignType \times WDigitString \times SignType \times WDigitString \times WDigitString} = (z \mapsto (\operatorname{sign}\left(\operatorname{re}\left(z\right) - \frac{1}{2}\right), unsignedThread\left(\operatorname{re}\left(z\right) - \frac{1}{2}\right), \operatorname{sign}\left(\operatorname{im}\left(z\right)\right), unsignedThread\left(\operatorname{im}\left(z\right)\right), \operatorname{wEncoding}\left(multiplicity\right)));\\{}let states: \operatorname{List}\left({SignType \times WDigitString \times SignType \times WDigitString \times WDigitString}\right) = [(\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), \operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right)), (\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), -\operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right)), (-\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), \operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right)), (-\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), -\operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right))];\\{}let orbitCodes: \operatorname{List}\left({SignType \times WDigitString \times SignType \times WDigitString \times WDigitString}\right) = [code\left(rho\right), code\left(\operatorname{conj}\left(rho\right)\right), code\left(1 - \operatorname{conj}\left(rho\right)\right), code\left(1 - rho\right)];\\{}code\left(\operatorname{conj}\left(rho\right)\right) = (\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), -\operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right)) \land\\{}code\left(1 - \operatorname{conj}\left(rho\right)\right) = (-\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), \operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right)) \land\\{}code\left(1 - rho\right) = (-\operatorname{sign}\left(delta\right), unsignedThread\left(delta\right), -\operatorname{sign}\left(gamma\right), unsignedThread\left(gamma\right), \operatorname{wEncoding}\left(multiplicity\right)) \land\\{}orbitCodes = states \land\\{}delta \ne 0 \Rightarrow \left(gamma \ne 0 \Rightarrow \operatorname{Nodup}\left(orbitCodes\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Symmetry/SignedZeckendorfOrbitCode.klein_actions_two_sign_bits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public code is constructed from the centered real coordinate, the height, their golden-scale W encodings, and the multiplicity W word. Conjugation, conjugate reflection, and reflection induce the three displayed sign transformations while preserving every unsigned word.

The orbit-code list is equal to the explicitly listed sign-state list. When both centered coordinates are nonzero, the sign values are nonzero and each differs from its negative, so the four entries are pairwise distinct.

## References

- Truth anchor: `D5/S3/Zeros/Symmetry/SignedZeckendorfOrbitCode.klein_actions_two_sign_bits`
- Dependency: [D5/S0/Conventions/WDigits](../../../S0/Conventions/WDigits.md)
