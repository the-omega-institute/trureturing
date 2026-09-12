# Logarithmic-Weight Coefficients Modulo Two

## Abstract

The logarithmic-weight coefficients are odd exactly at powers of two.

The parity clause of OEIS A397349 is quoted in hanna2026a397349. The frozen module LogarithmicWeightCatalanParity states this parity property as the proposition parity_conjecture without proof; this document records its proof. The entry's modulo-three clause is settled separately and is not restated here.

Write a for the frozen integer-valued function LogarithmicWeightCatalanParity.a. All indices and exponents are natural numbers. The result concerns that constructed sequence; no identification with the logarithmic generating function in the entry's NAME is asserted.

**Theorem 1.1 (Hanna's parity conjecture).**

$$\forall n: \mathbb{N}, (\operatorname{Odd}\left(\operatorname{a}\left(n\right)\right) \iff (\exists k: \mathbb{N}, n = 2^{k}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity.parity_conjecture_holds` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a397349-logarithmic-weight-parity` (proved) by `D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity.parity_conjecture_holds`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a397349-logarithmic-weight-parity","declaration_gid":"D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity.parity_conjecture_holds","resolution_kind":"proved"} -->

*Citation.* Paul D. Hanna (2026). *OEIS A397349, logarithmic-weight coefficients: residue and parity*. URL: <https://oeis.org/A397349>.

*Commentary.*

Let A be the coefficient series of a reduced modulo two, with X the indeterminate. Its constant coefficient is zero and its derivative is one. The convolution identities and their derivatives give A = X + A^2, the equation characterising the binary Catalan series with zero constant coefficient. Uniqueness identifies the two series, so the coefficients are odd exactly at powers of two, including n=1 and excluding n=0.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/LogarithmicWeightBinaryParity.parity_conjecture_holds`
- Dependency: [D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity](../Invariants/CatalanCompositionSquareParity.md)
- Dependency: [D5/S1/Recurrence/Residue/LogarithmicWeightCatalanParity](LogarithmicWeightCatalanParity.md)
