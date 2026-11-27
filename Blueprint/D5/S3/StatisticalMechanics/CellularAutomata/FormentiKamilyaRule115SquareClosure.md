# Question 2 for RESOCA 115 on the integer line

## Abstract

Three is a least period of a finite RESOCA 115 configuration, and nine is impossible.

**Theorem 1.1 (The realized least periods are not closed under squaring).**

$$\neg (\forall p \in \mathbb{N},\; \operatorname{RealizesLeastPeriod}\left(p\right) \Rightarrow \operatorname{RealizesLeastPeriod}\left(p^{2}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result` (`✓ std3`). ∎

*Resolves.* `Problems/formenti-kamilya-2026-resoca-115-question-2` (refuted) by `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"formenti-kamilya-2026-resoca-115-question-2","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Enrico Formenti, Supreeti Kamilya (2026). *The Curious Case of Reversible Elementary Second Order Cellular Automaton 115*. DOI: [10.4204/EPTCS.445.12](https://doi.org/10.4204/EPTCS.445.12). URL: <https://arxiv.org/abs/2606.13159v1>.

*Commentary.*

Section 3, Question 2 on printed p. 97 asks “If p is a period for RESOCA 115, is p² also a period?” The update is the second-order rule from Equation (1) and Table 1. RealizesLeastPeriod(p) means that p is positive and some ordered pair of past and current Boolean layers on the integer line returns as a full pair after p steps, with no return at any positive q < p. The union of the two initial supports must be finite, as in Section 2.1. The two occurrences of RealizesLeastPeriod quantify their configurations independently.

The all-zero pair has empty initial support. The theorem zero_period_three gives a return at three and excludes one and two. For any finite pair returning at nine, returns_three_of_returns_nine gives a return at three. Thus the implication in Question 2 fails at p = 3, since its consequent would require a pair with least period nine.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115SquareClosure.result`
- Dependency: [D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115](FormentiKamilyaRule115.md)
