# Thue Morse Factor Rigidity

## Abstract

For every integer ell at least two, a coding of a morphic word on a finite alphabet has unbounded abelian complexity and a strict hierarchy terminating at factor complexity.

**Definition 1.1 (factorComplexity).**

$$\forall (\operatorname{word} : \operatorname{Nat} \to \operatorname{Fin} 4) (\operatorname{n} : \operatorname{Nat}), \operatorname{factorComplexity} \operatorname{word} \operatorname{n} = (\operatorname{wordFactorSet} \operatorname{word} \operatorname{n}).\operatorname{card}$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseFactorRigidity.factorComplexity` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines factorComplexity.

**Definition 1.2 (binomialAt).**

$$\forall (\operatorname{word} : \operatorname{Nat} \to \operatorname{Fin} 4) (\operatorname{k} \operatorname{n} : \operatorname{Nat}), \operatorname{binomialAt} \operatorname{word} \operatorname{k} \operatorname{n} = \operatorname{binomialComplexity} \operatorname{word} \operatorname{k} \operatorname{n}$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseFactorRigidity.binomialAt` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines binomialAt.

**Definition 1.3 (Prec).**

$$\forall (\operatorname{f} \operatorname{g} : \operatorname{Nat} \to \operatorname{Nat}), \operatorname{Prec} \operatorname{f} \operatorname{g} \iff \operatorname{Set}.\operatorname{Infinite} \{\operatorname{n} | \operatorname{f} \operatorname{n} < \operatorname{g} \operatorname{n}\}$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseFactorRigidity.Prec` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines Prec.

**Definition 1.4 (Unbounded).**

$$\forall (\operatorname{f} : \operatorname{Nat} \to \operatorname{Nat}), \operatorname{Unbounded} \operatorname{f} \iff (\forall (\operatorname{bound} : \operatorname{Nat}), \exists (\operatorname{n} : \operatorname{Nat}), \operatorname{bound} < \operatorname{f} \operatorname{n})$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseFactorRigidity.Unbounded` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines Unbounded.

**Definition 1.5 (Hierarchy).**

$$\forall (\operatorname{word} : \operatorname{Nat} \to \operatorname{Fin} 4) (\operatorname{ell} : \operatorname{Nat}), \operatorname{Hierarchy} \operatorname{word} \operatorname{ell} \iff (\operatorname{Unbounded} (\operatorname{binomialAt} \operatorname{word} 1) \land (\forall (\operatorname{j} : \operatorname{Nat}), 1 \leq \operatorname{j} \to \operatorname{j} < \operatorname{ell} \to \operatorname{Prec} (\operatorname{binomialAt} \operatorname{word} \operatorname{j}) (\operatorname{binomialAt} \operatorname{word} (\operatorname{j} + 1))) \land (\forall (\operatorname{n} : \operatorname{Nat}), \operatorname{binomialAt} \operatorname{word} \operatorname{ell} \operatorname{n} = \operatorname{factorComplexity} \operatorname{word} \operatorname{n}))$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseFactorRigidity.Hierarchy` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

The displayed expression defines Hierarchy.

**Definition 1.6 (claim).**

$$\operatorname{claim} \iff (\forall (\operatorname{ell} : \operatorname{Nat}), 2 \leq \operatorname{ell} \to \exists (\operatorname{word} : \operatorname{Nat} \to \operatorname{Fin} 4), \operatorname{Hierarchy} \operatorname{word} \operatorname{ell})$$

*Formalization.* `D5/S1/Words/Complexity/ThueMorseFactorRigidity.claim` (`✓ std3`).

*Citation.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

Question C, arXiv:2201.04603v2, Section 7.1, PDF page 30: “For each ℓ ≥ 1, does there exist a word w (depending on ℓ) such that b_w^(1) is unbounded and b_w^(1) ≺ b_w^(2) ≺ ⋯ ≺ b_w^(ℓ−1) ≺ b_w^(ℓ) = p_w? If the answer is positive, can we find a (pure) morphic such word w?” The displayed proposition retains ℓ ≥ 2 and a four-letter alphabet, represented by Fin 4. Binomial profiles count every scattered pattern through the specified order; strict comparison means strict inequality at infinitely many lengths. The coding refinement is stated separately.

**Theorem 1.7 (morphic result).**

$$\forall (\operatorname{ell} : \operatorname{Nat}), 2 \leq \operatorname{ell} \to \exists (\operatorname{A} : \operatorname{Type}) (\operatorname{sigma} : \operatorname{A} \to \operatorname{List} \operatorname{A}) (\operatorname{a} : \operatorname{A}) (\operatorname{u} : \operatorname{Nat} \to \operatorname{A}) (\operatorname{code} : \operatorname{A} \to \operatorname{Fin} 4), \operatorname{Finite} \operatorname{A} \land \operatorname{Hierarchy} (\operatorname{code} \circ \operatorname{u}) \operatorname{ell} \land (\exists \operatorname{tail}, \operatorname{sigma} \operatorname{a} = \operatorname{a} :: \operatorname{tail} \land \operatorname{tail} \neq []) \land (\forall \operatorname{n} \operatorname{r} (\operatorname{hr} : \operatorname{r} < ((\operatorname{List}.\operatorname{flatMap} \operatorname{sigma})^{[\operatorname{n}]} [\operatorname{a}]).\operatorname{length}), \operatorname{u} \operatorname{r} = ((\operatorname{List}.\operatorname{flatMap} \operatorname{sigma})^{[\operatorname{n}]} [\operatorname{a}]).\operatorname{get} \langle \operatorname{r}, \operatorname{hr}\rangle ) \land (\forall \operatorname{bound}, \exists \operatorname{n}, \operatorname{bound} < ((\operatorname{List}.\operatorname{flatMap} \operatorname{sigma})^{[\operatorname{n}]} [\operatorname{a}]).\operatorname{length})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseFactorRigidity.morphic_result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

For every integer ell at least two, a coding of a morphic word on a finite alphabet has unbounded abelian complexity and a strict hierarchy terminating at factor complexity.

**Theorem 1.8 (result).**

$$\forall (\operatorname{ell} : \operatorname{Nat}), 2 \leq \operatorname{ell} \to \exists (\operatorname{word} : \operatorname{Nat} \to \operatorname{Fin} 4), \operatorname{Hierarchy} \operatorname{word} \operatorname{ell}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/ThueMorseFactorRigidity.result` (`✓ std3`). ∎

*Resolves.* `Problems/rigo-stipulanti-whiteland-question-c` (proved) by `D5/S1/Words/Complexity/ThueMorseFactorRigidity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rigo-stipulanti-whiteland-question-c","declaration_gid":"D5/S1/Words/Complexity/ThueMorseFactorRigidity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Michel Rigo; Manon Stipulanti; Markus A. Whiteland (2022). *Characterizations of families of morphisms and words via binomial complexities*. DOI: [10.1016/j.ejc.2024.103932](https://doi.org/10.1016/j.ejc.2024.103932). URL: <https://arxiv.org/abs/2201.04603v2>.

*Commentary.*

For every integer ell at least two, a coding of a morphic word on a finite alphabet has unbounded abelian complexity and a strict hierarchy terminating at factor complexity.

## References

- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.Hierarchy`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.Prec`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.Unbounded`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.binomialAt`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.claim`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.factorComplexity`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.morphic_result`
- Truth anchor: `D5/S1/Words/Complexity/ThueMorseFactorRigidity.result`
- Dependency: [D5/S0/Tower/GoldenGapWord](../../../S0/Tower/GoldenGapWord.md)
- Dependency: [D5/S1/Words/Complexity/LacunaryBinomialMarkers](LacunaryBinomialMarkers.md)
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](MorseHedlund.md)
- Dependency: [D5/S1/Words/Complexity/ThueMorsePositionalRecovery](ThueMorsePositionalRecovery.md)
- Dependency: [D5/S1/Words/Complexity/ThueMorseReducedAbelianOdd](ThueMorseReducedAbelianOdd.md)
- Dependency: [D5/S1/Words/Complexity/UniformWordRecurrence](UniformWordRecurrence.md)
- Dependency: [D5/S1/Words/Complexity/VivionBinomialConverseFails](VivionBinomialConverseFails.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
- Dependency: [D5/S1/Words/RankOneMorphismIterationBoundDefs](../RankOneMorphismIterationBoundDefs.md)
