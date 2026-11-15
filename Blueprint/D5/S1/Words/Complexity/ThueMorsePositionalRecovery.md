# Thue Morse Positional Recovery

## Abstract

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.1 (core last strict).**

$$\forall (\operatorname{k} : \mathbb{N}), \{\operatorname{n} | \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) (\operatorname{k} + 1) \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) (\operatorname{k} + 2) \operatorname{n}\}.\operatorname{Infinite}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_last_strict` (`✓ std3`). ∎

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.2 (core as expansion).**

$$\forall (\operatorname{r} \operatorname{k} : \operatorname{Nat}), \operatorname{core} (\operatorname{r} + \operatorname{k}) = \operatorname{uniformExpansion} (2 ^{\operatorname{r}}) (Nat.two_{pow_{pos}} r) (\operatorname{fun} \operatorname{a} \operatorname{i} \mapsto \operatorname{Bool}.\operatorname{xor} \operatorname{a} (\operatorname{thueMorse} \operatorname{val}\left(i\right))) (\operatorname{core} \operatorname{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_as_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The expansion uses the Fin-to-Nat value of each block index. The subscripted positivity proof spells the Lean constant Nat.two_pow_pos and introduces no new abbreviation.

**Theorem 1.3 (core middle strict).**

$$\forall (\operatorname{k} \operatorname{j} : \mathbb{N}), 2 \leq \operatorname{j} \to \operatorname{j} \leq \operatorname{k} \to \{\operatorname{n} | \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) \operatorname{j} \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) (\operatorname{j} + 1) \operatorname{n}\}.\operatorname{Infinite}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_middle_strict` (`✓ std3`). ∎

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.4 (top profile injectivity).**

$$\forall (\operatorname{k} \operatorname{n} : \operatorname{Nat}), \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} (\operatorname{k} + 2)) (\operatorname{wordFactorSet} (\operatorname{core} \operatorname{k}) \operatorname{n} : \operatorname{Set} (\operatorname{Fin} \operatorname{n} \to \operatorname{Bool}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.top_profile_injectivity` (`✓ std3`). ∎

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

## References

- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_as_expansion`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_last_strict`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_middle_strict`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.top_profile_injectivity`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore](ExactDecks/Growth/ExactDeckCore.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall](ExactDecks/Growth/PositiveWordBall.md)
- Dependency: [D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration](ExactDecks/UpperBound/OverlapInfiltration.md)
- Dependency: [D5/S1/Words/Complexity/LacunaryBinomialMarkers](LacunaryBinomialMarkers.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
- Dependency: [D5/S1/Words/Complexity/SubshiftTopology](SubshiftTopology.md)
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](ThueMorseReducedAbelianOdd.md)
- Dependency: [D5/S1/Words/Complexity/UniformWordRecurrence](UniformWordRecurrence.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](VivionBinomialConverseFails.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
- Dependency: [D5/S1/Words/ThueMorseDyadic](../ThueMorseDyadic.md)
- Dependency: [D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency](../TwoBlockSubstitution/ThueMorseFrequency.md)
