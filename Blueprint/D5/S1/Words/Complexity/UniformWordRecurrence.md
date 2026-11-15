# Uniform Word Recurrence

## Abstract

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Definition 1.1 (Recurrent).**

$$\forall (\operatorname{A} : \operatorname{Type}) [\operatorname{Fintype} \operatorname{A}] (\operatorname{x} : \operatorname{Nat} \to \operatorname{A}), \operatorname{Recurrent} \operatorname{x} \iff (\forall (\operatorname{n} : \operatorname{Nat}), \forall (\operatorname{u} : \operatorname{Fin} \operatorname{n} \to \operatorname{A}), \operatorname{u} \in \operatorname{wordFactorSet} \operatorname{x} \operatorname{n} \to \exists (\operatorname{R} : \operatorname{Nat}), \forall (\operatorname{s} : \operatorname{Nat}), \exists (\operatorname{t} : \operatorname{Nat}), \operatorname{s} \leq \operatorname{t} \land \operatorname{t} + \operatorname{n} \leq \operatorname{s} + \operatorname{R} \land \operatorname{u} = \operatorname{wordFactor} \operatorname{x} \operatorname{n} \operatorname{t})$$

*Formalization.* `D5/S1/Words/Complexity/UniformWordRecurrence.Recurrent` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines Recurrent.

**Definition 1.2 (uniformExpansion).**

$$\forall (\operatorname{A} \operatorname{B} : \operatorname{Type}) (\operatorname{q} : \operatorname{Nat}) (\operatorname{hq} : 0 < \operatorname{q}) (\operatorname{block} : \operatorname{A} \to \operatorname{Fin} \operatorname{q} \to \operatorname{B}) (\operatorname{x} : \operatorname{Nat} \to \operatorname{A}) (\operatorname{n} : \operatorname{Nat}), \operatorname{uniformExpansion} \operatorname{q} \operatorname{hq} \operatorname{block} \operatorname{x} \operatorname{n} = \operatorname{block} (\operatorname{x} (\operatorname{n} / \operatorname{q})) \langle \operatorname{n} \operatorname{mod} \operatorname{q}, \operatorname{by} \operatorname{omega}\rangle $$

*Formalization.* `D5/S1/Words/Complexity/UniformWordRecurrence.uniformExpansion` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines uniformExpansion. The operator / denotes natural-number floor division; mod denotes Nat.mod.

**Definition 1.3 (thueBlock).**

$$\forall (\operatorname{k} : \operatorname{Nat}) (\operatorname{a} : \operatorname{Bool}), \operatorname{thueBlock} \operatorname{k} \operatorname{a} = \operatorname{List}.\operatorname{ofFn} (\operatorname{fun} \operatorname{j} : \operatorname{Fin} (2 ^{\operatorname{k}}) \mapsto \operatorname{Bool}.\operatorname{xor} \operatorname{a} (\operatorname{thueMorse} \operatorname{j}))$$

*Formalization.* `D5/S1/Words/Complexity/UniformWordRecurrence.thueBlock` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines thueBlock.

**Theorem 1.4 (thueBlock zero).**

$$\forall (\operatorname{a} : \operatorname{Bool}), \operatorname{thueBlock} 0 \operatorname{a} = [\operatorname{a}]$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.thueBlock_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Theorem 1.5 (thueBlock succ).**

$$\forall (\operatorname{k} : \mathbb{N}) (\operatorname{a} : \operatorname{Bool}), \operatorname{thueBlock} (\operatorname{k} + 1) \operatorname{a} = \operatorname{thueBlock} \operatorname{k} \operatorname{a} ++ \operatorname{thueBlock} \operatorname{k} !\operatorname{a}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.thueBlock_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Definition 1.6 (core).**

$$\forall (\operatorname{k} \operatorname{n} : \operatorname{Nat}), \operatorname{core} \operatorname{k} \operatorname{n} = \operatorname{Bool}.\operatorname{xor} (!(\operatorname{goldenWord} (\operatorname{n} / (2 ^{\operatorname{k}})))) (\operatorname{thueMorse} (\operatorname{n} \operatorname{mod} (2 ^{\operatorname{k}})))$$

*Formalization.* `D5/S1/Words/Complexity/UniformWordRecurrence.core` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines core. The operator / denotes natural-number floor division; mod denotes Nat.mod.

**Theorem 1.7 (core recurrent).**

$$\forall (\operatorname{k} : \mathbb{N}), \operatorname{Recurrent} (\operatorname{core} \operatorname{k})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.core_recurrent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Definition 1.8 (thueWord).**

$$\forall (\operatorname{k} : \operatorname{Nat}) (\operatorname{source} : \operatorname{List} \operatorname{Bool}), \operatorname{thueWord} \operatorname{k} \operatorname{source} = \operatorname{List}.\operatorname{flatMap} (\operatorname{thueBlock} \operatorname{k}) \operatorname{source}$$

*Formalization.* `D5/S1/Words/Complexity/UniformWordRecurrence.thueWord` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines thueWord.

**Theorem 1.9 (thueWord of permutation).**

$$\forall (\operatorname{k} : \mathbb{N}) \{\operatorname{u} \operatorname{v} : \operatorname{List} \operatorname{Bool}\}, \operatorname{u}.\operatorname{Perm} \operatorname{v} \to \forall (\operatorname{pattern} : \operatorname{List} \operatorname{Bool}), \operatorname{pattern}.\operatorname{length} \leq \operatorname{k} + 1 \to \operatorname{scatteredCount} \operatorname{pattern} (\operatorname{thueWord} \operatorname{k} \operatorname{u}) = \operatorname{scatteredCount} \operatorname{pattern} (\operatorname{thueWord} \operatorname{k} \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.thueWord_of_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Definition 1.10 (tm).**

$$(\operatorname{tm} [] = []) \land (\forall (\operatorname{a} : \operatorname{Bool}) (\operatorname{source} : \operatorname{List} \operatorname{Bool}), \operatorname{tm} (\operatorname{a} :: \operatorname{source}) = \operatorname{a} :: (!\operatorname{a}) :: \operatorname{tm} \operatorname{source})$$

*Formalization.* `D5/S1/Words/Complexity/UniformWordRecurrence.tm` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines tm.

**Theorem 1.11 (tm length).**

$$\forall (\operatorname{source} : \operatorname{List} \operatorname{Bool}), (\operatorname{tm} \operatorname{source}).\operatorname{length} = 2 * \operatorname{source}.\operatorname{length}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.tm_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Theorem 1.12 (tm counts).**

$$\forall (\operatorname{source} : \operatorname{List} \operatorname{Bool}), \operatorname{scatteredCount} [\operatorname{false}] (\operatorname{tm} \operatorname{source}) = \operatorname{source}.\operatorname{length} \land \operatorname{scatteredCount} [\operatorname{true}] (\operatorname{tm} \operatorname{source}) = \operatorname{source}.\operatorname{length} \land \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] (\operatorname{tm} \operatorname{source}) = \operatorname{scatteredCount} [\operatorname{false}] \operatorname{source} + \operatorname{source}.\operatorname{length}.\operatorname{choose} 2 \land \operatorname{scatteredCount} [\operatorname{true}, \operatorname{true}] (\operatorname{tm} \operatorname{source}) = \operatorname{source}.\operatorname{length}.\operatorname{choose} 2 \land \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}, \operatorname{true}] (\operatorname{tm} \operatorname{source}) = \operatorname{scatteredCount} [\operatorname{false}, \operatorname{false}] \operatorname{source} + \operatorname{scatteredCount} [\operatorname{false}, \operatorname{true}] \operatorname{source} + \operatorname{source}.\operatorname{length}.\operatorname{choose} 3$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.tm_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Theorem 1.13 (repeated false count).**

$$\forall (\operatorname{source} : \operatorname{List} \operatorname{Bool}), \operatorname{scatteredCount} [\operatorname{false}, \operatorname{false}] \operatorname{source} = (\operatorname{scatteredCount} [\operatorname{false}] \operatorname{source}).\operatorname{choose} 2$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.repeated_false_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Theorem 1.14 (pair count snoc).**

$$\forall (\operatorname{a} \operatorname{b} \operatorname{c} : \operatorname{Bool}) (\operatorname{u} : \operatorname{List} \operatorname{Bool}), \operatorname{scatteredCount} [\operatorname{a}, \operatorname{b}] (\operatorname{u} ++ [\operatorname{c}]) = \operatorname{scatteredCount} [\operatorname{a}, \operatorname{b}] \operatorname{u} + \operatorname{if} \operatorname{b} = \operatorname{c} \operatorname{then} \operatorname{scatteredCount} [\operatorname{a}] \operatorname{u} \operatorname{else} 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.pair_count_snoc` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

**Theorem 1.15 (core first strict).**

$$\forall (\operatorname{k} : \mathbb{N}), 1 \leq \operatorname{k} \to \{\operatorname{n} | \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) 1 \operatorname{n} < \operatorname{binomialComplexity} (\operatorname{core} \operatorname{k}) 2 \operatorname{n}\}.\operatorname{Infinite}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/UniformWordRecurrence.core_first_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Uniform substitutions preserve recurrence. Dyadic Thue–Morse blocks have equal low-order scattered subword counts, with one additional order for permutations of source letters.

## References

- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.Recurrent`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.core`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.core_first_strict`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.core_recurrent`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.pair_count_snoc`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.repeated_false_count`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.thueBlock`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.thueBlock_succ`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.thueBlock_zero`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.thueWord`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.thueWord_of_permutation`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.tm`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.tm_counts`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.tm_length`
- Truth anchor: `D5/S1/Words/Complexity/UniformWordRecurrence.uniformExpansion`
- Dependency: [D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall](ExactDecks/Growth/PositiveWordBall.md)
- Dependency: [D5/S1/Words/Complexity/LacunaryBinomialMarkers](LacunaryBinomialMarkers.md)
- Dependency: [D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra](LyndonBrackets/LyndonBracketAlgebra.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra](PositivePairs/Coefficients/CutoffCoefficientAlgebra.md)
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients](PositivePairs/Coefficients/MagnusWordCoefficients.md)
- Dependency: [D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration](PositivePairs/Coefficients/PositivePairFiltration.md)
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](ThueMorseReducedAbelianOdd.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](VivionBinomialConverseFails.md)
- Dependency: [D5/S1/Words/GoldenUniformRecurrence](../GoldenUniformRecurrence.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
