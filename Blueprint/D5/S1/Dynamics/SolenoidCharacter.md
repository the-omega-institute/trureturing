# Characters of the Universal Solenoid

## Abstract

Continuous universal-solenoid characters are exactly rational coordinate characters.

**Theorem 1.1 (Continuous solenoid characters have unique rational slopes).**

$$\operatorname{Bijective}(\operatorname{rationalCharacterHom})$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/SolenoidCharacter.continuous_solenoid_characters_are_rational` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a reduced rational a/m, the corresponding character evaluates the m-th circle coordinate and multiplies it by a. The construction is additive in the rational slope. Conversely, continuity of an arbitrary character gives a finite coordinate whose kernel it kills. Restricting the character to the dense real flow and lifting through the real covering of the unit additive circle produces a continuous additive real map. Its slope times the killed coordinate index is an integer, so the slope is rational. Density proves equality on the whole solenoid, and a half-period argument proves uniqueness.

The pinned library was searched before construction. It provides AddCircle.isCoveringMap_coe, IsCoveringMap.existsUnique_continuousMap_lifts, map_real_smul, AddCircle.coe_eq_zero_iff, and the finite-circle torsion lemmas AddCircle.nsmul_eq_zero_iff and ZMod.toAddCircle. It does not provide a universal-solenoid dual classification or a packaged classification of continuous unit-circle endomorphisms. The deposited result is therefore a new proof assembled from those library primitives, not a thin wrapper. The source atom carries no numerical certificate.

## References

- Truth anchor: `D5/S1/Dynamics/SolenoidCharacter.continuous_solenoid_characters_are_rational`
