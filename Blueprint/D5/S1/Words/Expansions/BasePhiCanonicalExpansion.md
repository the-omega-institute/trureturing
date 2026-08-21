# Canonical Two-Sided Base-Phi Expansion

## Abstract

Natural numbers have a unique finite two-sided canonical base-phi expansion.

**Theorem 1.1 (Canonical two-sided digits exist uniquely).**

$$\forall N\in\mathbb{N},\ \exists ! digits,\ \operatorname{Canonical}(digits) \land \operatorname{basePhiValue}(digits)=N$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Expansions/BasePhiCanonicalExpansion.canonical_two_sided_digits_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number N there is exactly one finitely supported integer-indexed digit word with digits at most one, no adjacent ones, and base-phi value equal to N. Uniqueness is proved independently by shifting both finite supports into the nonnegative indices and reading the resulting phi powers as Fibonacci weights. Existence is constructed by a contracting conjugate-window argument.

## References

- Truth anchor: `D5/S1/Words/Expansions/BasePhiCanonicalExpansion.canonical_two_sided_digits_unique`
- Dependency: [D5/S1/Digit/Carry/Successor](../../Digit/Carry/Successor.md)
