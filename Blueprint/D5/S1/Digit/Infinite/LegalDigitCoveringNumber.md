# Minimum Covers of the Legal Digit Space

## Abstract

Minimum Covers of the Legal Digit Space.

**Theorem 1.1 (Fibonacci minimum covering number).**

Lean statement: `D5/S1/Digit/Infinite/LegalDigitCoveringNumber.least_covering_number`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/LegalDigitCoveringNumber.least_covering_number` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real radius parameter strictly between zero and one, the least number of closed balls of radius theta to the L covering legal infinite Boolean digits is the Fibonacci count of admissible length L prefixes. The proof realizes every admissible prefix by zero extension and shows that every ball is contained in one prefix cylinder.

## References

- Truth anchor: `D5/S1/Digit/Infinite/LegalDigitCoveringNumber.least_covering_number`
- Dependency: [D5/S1/Digit/Infinite/SuccessorContinuity](SuccessorContinuity.md)
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../Words/AdmissibleWords/AdmissibleCount.md)
