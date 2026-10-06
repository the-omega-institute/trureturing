# Characteristic-three flat-plus-spike ambiguity

## Abstract

For a finite field of characteristic three, the normalized flat-plus-spike
state has an explicit additive-character ambiguity formula.  Every nonidentity
coefficient has a dimension-independent normalized intensity floor.  The
projector-Gram/Rayleigh bridge from issue #13556 remains a separate open
boundary.

**Definition 1.1 (Flat-plus-spike state).**

Lean statement: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState`

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState` (`✓ std3`).

*Source.* Zhu--Wang, arXiv:2608.11850v1, equation (62), with the phase-zero
specialization; the characteristic-three analysis is repository-derived.

For a finite field `K`, write `q = |K|`, `s = sqrt(q)`, and `N = 2q + 2s`.
The state has coordinate `(1 + s * 1_{x=0}) / sqrt(N)`.

**Definition 1.2 (Finite-character ambiguity).**

Lean statement: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.ambiguity`

*Formalization.* `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.ambiguity` (`✓ std3`).

For an additive character `psi`, a function `f`, and labels `a,b`, the
ambiguity coefficient is
`sum_x conj (f x) * psi (b * (x-a)) * f (x-a)`.

**Theorem 1.3 (Coordinate normalization).**

Lean statement: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_normalized`

*Proof.* Machine-checked in Lean as
`D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_normalized` (`✓ std3`). ∎

The squared coordinate moduli sum to one for every finite field.

**Theorem 1.4 (Exact ambiguity formula).**

Lean statement: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_ambiguity`

*Proof.* Machine-checked in Lean as
`D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_ambiguity` (`✓ std3`). ∎

For every nontrivial additive character,

`A(a,b) = (q 1_{b=0} + q 1_{a=0} + s (1 + psi(-ba))) / N`.

The character sum is evaluated with Mathlib's primitive-character API.

**Theorem 1.5 (Characteristic-three intensity floor).**

Lean statement: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_intensity_lower_bound`

*Proof.* Machine-checked in Lean as
`D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_intensity_lower_bound` (`✓ std3`). ∎

If `K` has characteristic three and `(a,b) != (0,0)`, then

`1 / (4 (sqrt(q) + 1)^2) <= normSq (A(a,b))`.

The proof uses `psi(x)^3 = 1` and the cubic-root estimate
`1 <= normSq (1 + psi(x))`.

**Theorem 1.6 (Uniform ambiguity-side SIC scale).**

Lean statement: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_uniform_ambiguity_bound`

*Proof.* Machine-checked in Lean as
`D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_uniform_ambiguity_bound` (`✓ std3`). ∎

For every nontrivial character and every nonidentity label, the state is
normalized and `(q+1) * normSq(A(a,b)) >= 1/8`.

## Remaining boundary for issue #13556

This module does not define the canonical trace character on every
`F_(3^r)`, the finite-field Weyl displacement/projector family, or the
projector-Gram Fourier/Rayleigh identity.  Consequently it does not claim the
full uniform-stability theorem or POVM completeness.  The proved intensity
bound supplies the constant `1/8` once that independent bridge is formalized.

## References

- Source note: [Zhu--Wang, arXiv:2608.11850v1](../../../../../Library/Quantum/zhu2026stable.md)
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_normalized`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_ambiguity`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_intensity_lower_bound`
- Truth anchor: `D5/S3/Quantum/Measurement/CharacteristicThreeSpikeAmbiguity.spikeState_uniform_ambiguity_bound`
