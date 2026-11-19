# Thue Morse Positional Recovery

## Abstract

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Definition 1.1 (reversePolynomial).**

$$\forall (\operatorname{u} : \operatorname{List} \operatorname{Bool}), \operatorname{reversePolynomial} \operatorname{u} = \operatorname{Polynomial}.\operatorname{ofCoeffList} (\operatorname{List}.\operatorname{map} (\operatorname{fun} \operatorname{a} : \operatorname{Bool} \mapsto (\operatorname{sign} \operatorname{a} : \mathbb{Q})) (\operatorname{List}.\operatorname{reverse} \operatorname{u}))$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.reversePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines reversePolynomial.

**Theorem 1.2 (ofCoeffList append).**

$$\forall (\operatorname{u} \operatorname{v} : \operatorname{List} \mathbb{Q}), \operatorname{Polynomial}.\operatorname{ofCoeffList} (\operatorname{u} ++ \operatorname{v}) = \operatorname{Polynomial}.\operatorname{ofCoeffList} \operatorname{u} + \operatorname{Polynomial}.\operatorname{X} ^{\operatorname{u}.\operatorname{length}} * \operatorname{Polynomial}.\operatorname{ofCoeffList} \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.ofCoeffList_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.3 (positional coeff eq of counts).**

$$\forall (\operatorname{m} : \mathbb{N}) (\operatorname{u} \operatorname{v} : \operatorname{List} \operatorname{Bool}), (\forall (\operatorname{p} : \operatorname{List} \operatorname{Bool}), \operatorname{p}.\operatorname{length} \leq \operatorname{m} \to \operatorname{scatteredCount} \operatorname{p} \operatorname{u} = \operatorname{scatteredCount} \operatorname{p} \operatorname{v}) \to \forall \operatorname{r} < \operatorname{m}, ((\operatorname{reversePolynomial} \operatorname{u} - \operatorname{reversePolynomial} \operatorname{v}).\operatorname{comp} (\operatorname{Polynomial}.\operatorname{X} + 1)).\operatorname{coeff} \operatorname{r} = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.positional_coeff_eq_of_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.4 (root power dvd of translated coeff).**

$$\forall (\operatorname{p} : \operatorname{Polynomial} \mathbb{Q}) (\operatorname{m} : \mathbb{N}), (\forall \operatorname{r} < \operatorname{m}, (\operatorname{p}.\operatorname{comp} (\operatorname{Polynomial}.\operatorname{X} + 1)).\operatorname{coeff} \operatorname{r} = 0) \to (\operatorname{Polynomial}.\operatorname{X} - 1) ^{\operatorname{m}} \mid \operatorname{p}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.root_power_dvd_of_translated_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.5 (reverse tm).**

$$\forall (\operatorname{u} : \operatorname{List} \operatorname{Bool}), \operatorname{reversePolynomial} (\operatorname{tm} \operatorname{u}) = (\operatorname{Polynomial}.\operatorname{X} - 1) * (\operatorname{reversePolynomial} \operatorname{u}).\operatorname{comp} (\operatorname{Polynomial}.\operatorname{X} ^{2})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.reverse_tm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.6 (recover counts of moments).**

$$\forall (\operatorname{u} \operatorname{v} : \operatorname{List} \operatorname{Bool}), \operatorname{u}.\operatorname{length} = \operatorname{v}.\operatorname{length} \to \operatorname{Polynomial}.\operatorname{eval} 1 (\operatorname{reversePolynomial} \operatorname{u}) = \operatorname{Polynomial}.\operatorname{eval} 1 (\operatorname{reversePolynomial} \operatorname{v}) \to \operatorname{Polynomial}.\operatorname{eval} 1 (\operatorname{Polynomial}.\operatorname{derivative} (\operatorname{reversePolynomial} \operatorname{u})) = \operatorname{Polynomial}.\operatorname{eval} 1 (\operatorname{Polynomial}.\operatorname{derivative} (\operatorname{reversePolynomial} \operatorname{v})) \to \operatorname{scatteredCount} [\operatorname{false}] \operatorname{u} = \operatorname{scatteredCount} [\operatorname{false}] \operatorname{v} \land \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] \operatorname{u} = \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.recover_counts_of_moments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.7 (iterate eq thueWord).**

$$\forall (\operatorname{k} : \operatorname{Nat}) (\operatorname{u} : \operatorname{List} \operatorname{Bool}), \operatorname{Nat}.\operatorname{iterate} \operatorname{tm} \operatorname{k} \operatorname{u} = \operatorname{thueWord} \operatorname{k} \operatorname{u}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.iterate_eq_thueWord` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.8 (counts two of zero pair).**

$$\forall (\operatorname{u} \operatorname{v} : \operatorname{List} \operatorname{Bool}), \operatorname{u}.\operatorname{length} = \operatorname{v}.\operatorname{length} \to \operatorname{scatteredCount} [\operatorname{false}] \operatorname{u} = \operatorname{scatteredCount} [\operatorname{false}] \operatorname{v} \to \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] \operatorname{u} = \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] \operatorname{v} \to \forall (\operatorname{p} : \operatorname{List} \operatorname{Bool}), \operatorname{p}.\operatorname{length} \leq 2 \to \operatorname{scatteredCount} \operatorname{p} \operatorname{u} = \operatorname{scatteredCount} \operatorname{p} \operatorname{v}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.counts_two_of_zero_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.9 (core last strict).**

$$\forall (\operatorname{k} : \mathbb{N}), \{\operatorname{n} | \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) (\operatorname{k} + 1) \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) (\operatorname{k} + 2) \operatorname{n}\}.\operatorname{Infinite}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_last_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.10 (expanded aligned factor).**

$$\forall (\operatorname{w} : \operatorname{Nat} \to \operatorname{Bool}) (\operatorname{r} \operatorname{n} \operatorname{s} : \operatorname{Nat}), \operatorname{List}.\operatorname{ofFn} (\operatorname{wordFactor} (\operatorname{uniformExpansion} (2 ^{\operatorname{r}}) (\operatorname{by} \operatorname{positivity}) (\operatorname{fun} \operatorname{a} \operatorname{i} \mapsto \operatorname{Bool}.\operatorname{xor} \operatorname{a} (\operatorname{thueMorse} \operatorname{i})) \operatorname{w}) (2 ^{\operatorname{r}} * \operatorname{n}) (2 ^{\operatorname{r}} * \operatorname{s})) = \operatorname{thueWord} \operatorname{r} (\operatorname{List}.\operatorname{ofFn} (\operatorname{wordFactor} \operatorname{w} \operatorname{n} \operatorname{s}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.expanded_aligned_factor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.11 (core as expansion).**

$$\forall (\operatorname{r} \operatorname{k} : \operatorname{Nat}), \operatorname{core} (\operatorname{r} + \operatorname{k}) = \operatorname{uniformExpansion} (2 ^{\operatorname{r}}) (\operatorname{by} \operatorname{positivity}) (\operatorname{fun} \operatorname{a} \operatorname{i} \mapsto \operatorname{Bool}.\operatorname{xor} \operatorname{a} (\operatorname{thueMorse} \operatorname{i})) (\operatorname{core} \operatorname{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_as_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.12 (core middle strict).**

$$\forall (\operatorname{k} \operatorname{j} : \mathbb{N}), 2 \leq \operatorname{j} \to \operatorname{j} \leq \operatorname{k} \to \{\operatorname{n} | \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) \operatorname{j} \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) (\operatorname{j} + 1) \operatorname{n}\}.\operatorname{Infinite}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_middle_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Definition 1.13 (frame).**

$$\forall (\operatorname{l} \operatorname{r} : \operatorname{Option} \operatorname{Bool}) (\operatorname{u} : \operatorname{List} \operatorname{Bool}), \operatorname{frame} \operatorname{l} \operatorname{u} \operatorname{r} = \operatorname{l}.\operatorname{toList} ++ \operatorname{tm} \operatorname{u} ++ \operatorname{r}.\operatorname{toList}$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.frame` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines frame.

**Theorem 1.14 (frame alignment).**

$$\forall (\operatorname{l} \operatorname{r} \operatorname{l}' \operatorname{r}' : \operatorname{Option} \operatorname{Bool}) (\operatorname{u} \operatorname{v} : \operatorname{List} \operatorname{Bool}), (\operatorname{frame} \operatorname{l} \operatorname{u} \operatorname{r}).\operatorname{length} = (\operatorname{frame} \operatorname{l}' \operatorname{v} \operatorname{r}').\operatorname{length} \to \operatorname{scatteredCount} [\operatorname{false}] (\operatorname{frame} \operatorname{l} \operatorname{u} \operatorname{r}) = \operatorname{scatteredCount} [\operatorname{false}] (\operatorname{frame} \operatorname{l}' \operatorname{v} \operatorname{r}') \to \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] (\operatorname{frame} \operatorname{l} \operatorname{u} \operatorname{r}) = \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] (\operatorname{frame} \operatorname{l}' \operatorname{v} \operatorname{r}') \to \operatorname{l} = \operatorname{l}' \land \operatorname{r} = \operatorname{r}' \land \operatorname{u}.\operatorname{length} = \operatorname{v}.\operatorname{length} \lor \operatorname{frame} \operatorname{l} \operatorname{u} \operatorname{r} = \operatorname{frame} \operatorname{l}' \operatorname{v} \operatorname{r}'$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.frame_alignment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Definition 1.15 (mu).**

$$\forall (\operatorname{w} : \operatorname{Nat} \to \operatorname{Bool}) (\operatorname{n} : \operatorname{Nat}), \operatorname{mu} \operatorname{w} \operatorname{n} = \operatorname{Bool}.\operatorname{xor} (\operatorname{w} (\operatorname{n} / 2)) (\operatorname{thueMorse} (\operatorname{n} \operatorname{mod} 2))$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.mu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines mu. The operator / denotes natural-number floor division; mod denotes Nat.mod.

**Theorem 1.16 (factor frame).**

$$\forall (\operatorname{w} : \operatorname{Nat} \to \operatorname{Bool}) (\operatorname{n} \operatorname{s} : \operatorname{Nat}), \exists (\operatorname{l} \operatorname{r} : \operatorname{Option} \operatorname{Bool}) (\operatorname{m} \operatorname{t} : \operatorname{Nat}), \operatorname{List}.\operatorname{ofFn} (\operatorname{wordFactor} (\operatorname{mu} \operatorname{w}) \operatorname{n} \operatorname{s}) = \operatorname{frame} \operatorname{l} (\operatorname{List}.\operatorname{ofFn} (\operatorname{wordFactor} \operatorname{w} \operatorname{m} \operatorname{t})) \operatorname{r}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.factor_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

**Theorem 1.17 (top profile injectivity).**

$$\forall (\operatorname{k} \operatorname{n} : \operatorname{Nat}), \operatorname{Set}.\operatorname{InjOn} (\operatorname{binomialProfile} (\operatorname{k} + 2)) (\operatorname{wordFactorSet} (\operatorname{core} \operatorname{k}) \operatorname{n} : \operatorname{Set} (\operatorname{Fin} \operatorname{n} \to \operatorname{Bool}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.top_profile_injectivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Signed positional polynomials transport moments through Thue–Morse substitution. Golden factors then yield strict inequalities between successive binomial complexities.

## References

- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_as_expansion`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_last_strict`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.core_middle_strict`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.counts_two_of_zero_pair`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.expanded_aligned_factor`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.factor_frame`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.frame`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.frame_alignment`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.iterate_eq_thueWord`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.mu`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.ofCoeffList_append`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.positional_coeff_eq_of_counts`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.recover_counts_of_moments`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.reversePolynomial`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.reverse_tm`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorsePositionalRecovery.root_power_dvd_of_translated_coeff`
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
