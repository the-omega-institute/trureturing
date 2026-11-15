# CassaigneSturmianCharacterization

## Abstract

Uniform replication and golden-word asymptotic invariants.

**Definition 1.1 (claim).**

$$\operatorname{claim}=(\forall \operatorname{u} : \operatorname{Nat} \to \operatorname{Bool} , \operatorname{indStar} \operatorname{u} = \operatorname{rhoStar} \operatorname{u} \to \operatorname{IsSturmian} \operatorname{u})$$

*Formalization.* `D5/S1/Words/Complexity/CassaigneSturmianCharacterization.claim` (`✓ std3`).

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Printed p. 707, Open problem 2: “Open problem 2. How can this equality be explained? Does it characterize Sturmian words? (Compare, for instance, with the Prouhet-Thue-Morse word which has ind*(t) = 2 and ρ*(t) = 10, see Prop. 6.1.)” The alphabet is Bool with true representing a; natural indices start at zero. The implication ranges over every infinite binary word.

**Theorem 1.2 (result).**

$$\neg (\forall \operatorname{u} : \operatorname{Nat} \to \operatorname{Bool} , \operatorname{indStar} \operatorname{u} = \operatorname{rhoStar} \operatorname{u} \to \operatorname{IsSturmian} \operatorname{u})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result` (`✓ std3`). ∎

*Resolves.* `Problems/cassaigne-sturmian` (refuted) by `D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cassaigne-sturmian","declaration_gid":"D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

Replicating each letter of the golden word twice gives equal finite asymptotic invariants, both ENNReal.ofReal (2 + Real.goldenRatio). It contains both constant binary bigrams, which the irrational mechanical codings cannot contain together. The equality therefore fails to imply the stated mechanical representation. The argument treats every replication factor at least two and does not classify all equality cases.

## References

- Truth anchor: `D5/S1/Words/Complexity/CassaigneSturmianCharacterization.claim`
- Truth anchor: `D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result`
- Dependency: [D5/S1/Words/Complexity/CassaigneIndexTransport](CassaigneIndexTransport.md)
- Dependency: [D5/S1/Words/Complexity/CassaigneRecurrenceTransport](CassaigneRecurrenceTransport.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
- Dependency: [D5/S1/Words/ReturnWords/CassaigneGoldenRecurrence](../ReturnWords/CassaigneGoldenRecurrence.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenSharpRepetitions](../ReturnWords/GoldenSharpRepetitions.md)
