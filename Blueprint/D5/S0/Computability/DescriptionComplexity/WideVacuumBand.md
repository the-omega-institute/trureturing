# Wide Vacuum Band

## Abstract

A finite low-cost cover leaves binary records with unbounded spectrum gaps.

**Theorem 1.1 (Finite low-cost covers leave arbitrarily wide gaps).**

$$\exists c_0, c_1\in \mathbb{N}, (\forall n \geq 2, \exists R_n, |R_n| = n \land \operatorname{BinaryCoordinates}(R_n) \land K_{entry}(R_n) \le c_0\\\land k_{min}(R_n) \geq n - c_1 \land \operatorname{width}(R_n) \geq n - c_0 - c_1) \land\\(\forall W\in \mathbb{N}, \exists n \geq 2, R_n, |R_n| = n \land \operatorname{BinaryCoordinates}(R_n) \land K_{entry}(R_n) \le c_0 \land k_{min}(R_n) \geq n - c_1 \land W \le \operatorname{width}(R_n)).$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/DescriptionComplexity/WideVacuumBand.arbitrarily_wide_vacuum_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each size n, the model supplies a finite family of admissible binary records. Every record has entry cost at most the fixed constant c0. The existing spectrum-bottom definition is the least cost of a total program consistent with a record.

Every program below the fixed n - c1 threshold is listed in a finite family. The sum of its consistency-fiber cardinalities is strictly smaller than the admissible-record cardinality. Mathlib's finite-union cardinality bound therefore leaves an uncovered record, and its least consistent-program cost is at least n - c1.

Natural-number subtraction gives width at least n - c0 - c1. Choosing n larger than any requested width proves unboundedness. Algorithmic complexity semantics and the source counting estimate remain explicit model premises rather than being redefined or re-proved here.

## References

- Truth anchor: `D5/S0/Computability/DescriptionComplexity/WideVacuumBand.arbitrarily_wide_vacuum_band`
- Dependency: [D5/S0/Computability/DescriptionComplexity/LookupProgramUpperBound](LookupProgramUpperBound.md)
