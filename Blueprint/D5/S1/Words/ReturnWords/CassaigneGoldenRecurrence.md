# CassaigneGoldenRecurrence

## Abstract

Uniform replication and golden-word asymptotic invariants.

**Theorem 1.1 (golden rhoStar eq sharp).**

$$\operatorname{rhoStar} \operatorname{goldenWord} = \operatorname{ENNReal.ofReal} (2 + \operatorname{Real.goldenRatio})$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ReturnWords/CassaigneGoldenRecurrence.golden_rhoStar_eq_sharp` (`✓ std3`). ∎

*Citation.* Julien Cassaigne (2008). *On extremal properties of the Fibonacci word*. DOI: [10.1051/ita:2008003](https://doi.org/10.1051/ita:2008003). URL: <https://www.numdam.org/item/10.1051/ita:2008003.pdf>.

*Commentary.*

The displayed statement uses natural indices. Division of natural numbers is Nat.div; subtraction of natural numbers is truncated. Casts to Real, ENat and ENNReal are displayed with their codomains.

## References

- Truth anchor: `D5/S1/Words/ReturnWords/CassaigneGoldenRecurrence.golden_rhoStar_eq_sharp`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S0/Tower/GoldenGapWord](../../../S0/Tower/GoldenGapWord.md)
- Dependency: [D5/S1/Words/Complexity/CassaigneRecurrenceTransport](../Complexity/CassaigneRecurrenceTransport.md)
- Dependency: [D5/S1/Words/GoldenMechanicalWord](../GoldenMechanicalWord.md)
- Dependency: [D5/S1/Words/GoldenUniformRecurrence](../GoldenUniformRecurrence.md)
- Dependency: [D5/S1/Words/GoldenWord](../GoldenWord.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenArcFirstReturn](GoldenArcFirstReturn.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenArcFirstReturnCore](GoldenArcFirstReturnCore.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenReturnWords](GoldenReturnWords.md)
- Dependency: [D5/S1/Words/ReturnWords/GoldenSharpRepetitions](GoldenSharpRepetitions.md)
