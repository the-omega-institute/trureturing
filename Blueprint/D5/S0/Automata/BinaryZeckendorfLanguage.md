# The Exact Binary Base Language

## Abstract

The successful language of the binary Zeckendorf base is exactly nonadjacency.

**Theorem 1.1 (Successful execution is equivalent to no adjacent ones).**

$$\forall w : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), {\exists q : BinaryZeckendorfState, \operatorname{evalBinaryZeckendorfBase}\left(w\right) = \operatorname{some}\left(q\right)} \iff \operatorname{NoAdjacentOnes}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/BinaryZeckendorfLanguage.base_success_iff_noAdjacentOnes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The word w is any list over Fin 2. The base begins in previousZero; q ranges over BinaryZeckendorfState. NoAdjacentOnes means that each adjacent pair contains a zero. There is no leading-one or nonempty-word premise.

The proof strengthens the induction by recording the preceding bit in the initial base state. It handles both initial states and both symbols, so it also excludes undefined runs caused by adjacent ones.

## References

- Truth anchor: `D5/S0/Automata/BinaryZeckendorfLanguage.base_success_iff_noAdjacentOnes`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](TypedPartialDFAOOverBase.md)
