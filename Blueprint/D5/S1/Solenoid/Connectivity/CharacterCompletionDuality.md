# Character Groups of the Two Completions

## Abstract

Profinite and solenoid completions recover their rational continuous character groups.

**Theorem 1.1 (The two completion character loops close).**

$$(\forall chi: \operatorname{ContinuousAddCharacters}\left(ProfiniteIntegers, UnitAddCircle\right), \operatorname{rationalCircleEmbedding}\left(\operatorname{profiniteCharacterEquivRationalCircle}\left(chi\right)\right) = \operatorname{profiniteCharacterAtOne}\left(chi\right)) \land\\{}(\forall psi: \operatorname{ContinuousAddCharacters}\left(UniversalSolenoid, UnitAddCircle\right), \operatorname{rationalCharacterHom}\left(\operatorname{characterEquivRational}\left(psi\right)\right) = psi).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/Connectivity/CharacterCompletionDuality.character_completion_duality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous character of the compatible-residue profinite integers is determined by its value at the dense integer generator. Finite-residue factorization makes that value a rational phase, and explicit residue characters realize every rational phase modulo integers. The resulting additive equivalence is characterized by this evaluation equation.

For the universal solenoid, the frozen rational-slope equivalence is reused directly. Its inverse computation equation says that reconstructing a coordinate character from the recovered rational slope returns the original continuous character.

Repository body-shape search found the finite-residue factorization and the complete solenoid classification, but no profinite rational-phase equivalence. Pinned Mathlib contributes generic range equivalences only; it has no exact classification on these carriers.

## References

- Truth anchor: `D5/S1/Solenoid/Connectivity/CharacterCompletionDuality.character_completion_duality`
- Dependency: [D5/S1/Dynamics/ProfiniteCharacter](../../Dynamics/ProfiniteCharacter.md)
- Dependency: [D5/S1/Dynamics/SolenoidCharacter](../../Dynamics/SolenoidCharacter.md)
