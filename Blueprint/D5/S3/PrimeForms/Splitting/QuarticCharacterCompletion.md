# Quartic Character Completion Modulo Sixty

## Abstract

A quartic modulo-five character completes the mod-sixty splitting profile.

**Definition 1.1 (The Gaussian quadratic character).**

$$chi_{-4}: (\mathbb{Z}/60\mathbb{Z})^{\times} \to mu_{2}.$$

*Formalization.* `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.chiMinusFour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Gaussian split-inert reading is composed with the standard binary root character to obtain a homomorphism into mu two.

**Definition 1.2 (The Eisenstein quadratic character).**

$$chi_{-3}: (\mathbb{Z}/60\mathbb{Z})^{\times} \to mu_{2}.$$

*Formalization.* `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.chiMinusThree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Eisenstein split-inert reading is composed with the same standard binary root character.

**Definition 1.3 (The quartic modulo-five character).**

$$psi_{5}: (\mathbb{Z}/60\mathbb{Z})^{\times} \to mu_{4}.$$

*Formalization.* `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psiFive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Reduction from units modulo sixty to units modulo five is followed by the discrete logarithm base two and the standard character into the fourth roots of unity.

The discrete logarithm table is total on the four unit residues. Its identity and multiplication laws are checked on that finite group, so the definition is representative-independent.

**Definition 1.4 (The quadratic-quadratic-quartic completion).**

$$Psi_{60} = (chi_{-4}, chi_{-3}, psi_{5}): (\mathbb{Z}/60\mathbb{Z})^{\times} \to mu_{2} \times mu_{2} \times mu_{4}.$$

*Formalization.* `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psiSixty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The completed map records the Gaussian and Eisenstein quadratic characters together with the quartic modulo-five character.

**Theorem 1.5 (The modulo-five generator maps to i).**

$$psi_{5}(7) = i.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psi_five_maps_mod_five_generator_two_to_i` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The unit class seven reduces to the generator two modulo five. Its discrete logarithm is one, so the standard quartic character takes the value i.

**Theorem 1.6 (The quartic completion separates every unit class).**

$$\forall u, v: (\mathbb{Z}/60\mathbb{Z})^{\times}, Psi_{60}(u) = Psi_{60}(v) \Rightarrow u = v.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psi_sixty_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of completed values recovers the Gaussian and Eisenstein readings and the full modulo-five residue.

These data give equal three-ring profiles and equal orientation bits. The preceding orientation theorem then forces the two unit classes to be equal.

**Theorem 1.7 (The quartic coordinate strictly improves the binary profile).**

$$\exists u, v: (\mathbb{Z}/60\mathbb{Z})^{\times}, u \neq v \land\\{}triRingImage(u) = triRingImage(v) \land\\{}Psi_{60}(u) \neq Psi_{60}(v).$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.quadratic_profile_collision_but_quartic_completion_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The distinct classes one and forty-nine have the same three-ring binary profile, while the completed character values differ. This is the concrete mu-two-cubed versus mu-two-squared times mu-four contrast.

## References

- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.chiMinusFour`
- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.chiMinusThree`
- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psiFive`
- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psiSixty`
- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psi_five_maps_mod_five_generator_two_to_i`
- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.psi_sixty_injective`
- Truth anchor: `D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.quadratic_profile_collision_but_quartic_completion_separates`
- Dependency: [D5/S3/Factorization/Galois/GeneralPowerCharacterLayer](../../Factorization/Galois/GeneralPowerCharacterLayer.md)
- Dependency: [D5/S3/PrimeForms/Splitting/ModFiveOrientationBit](ModFiveOrientationBit.md)
- Dependency: [D5/S3/PrimeForms/Splitting/QuadraticCharacterProfileRedundancy](QuadraticCharacterProfileRedundancy.md)
