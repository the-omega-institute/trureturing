# Finite Description Codes in PZG Tables

## Abstract

Shifted prime-sequence description codes embed into canonical PZG tables.

**Theorem 1.1 (Finite description codes have canonical PZG tables).**

$$\forall D \in \operatorname{List}(\mathbb{N}),\ \operatorname{primeAxisEncoding}(\operatorname{finiteDescriptionPZGCode}(D)) = \operatorname{positivePrimeSequenceCode}(D) \land \operatorname{decodePrimeAxisTable}(\operatorname{finiteDescriptionPZGCode}(D)) = \operatorname{primeSequenceCode}(D).$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PrimeAxis/FiniteDescriptionPZGCode.finite_description_pzg_code_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite description is represented here by a finite sequence of natural numbers. Its shifted prime-power code is always positive, including for the empty description, and therefore lies in the positive-natural codomain of the established primeAxisEncoding equivalence.

Applying the inverse equivalence produces a canonical PrimeAxisTable. The forward equivalence returns exactly the original shifted prime-sequence code, and decodePrimeAxisTable recovers its underlying natural number.

This theorem supplies only the generic PZG membership bridge. It does not assert a kernel self-code fixed point: the repository does not yet define a particular kernel, its finite syntax description, or a kernel self-code operator.

## References

- Truth anchor: `D5/S1/Digit/PrimeAxis/FiniteDescriptionPZGCode.finite_description_pzg_code_spec`
- Dependency: [D5/S0/History/PrimeSequenceCode](../../../S0/History/PrimeSequenceCode.md)
- Dependency: [D5/S1/Digit/PrimeAxisEncoding](../PrimeAxisEncoding.md)
