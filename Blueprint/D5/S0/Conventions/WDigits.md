# W-Digit Convention

## Abstract

W digits use shifted Fibonacci weights and the canonical Zeckendorf representation.

**Definition 1.1 (Every natural has exactly one canonical W-digit representation).**

Lean statement: `D5/S0/Conventions/WDigits.wEncoding`

*Formalization.* `D5/S0/Conventions/WDigits.wEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural numbers are equivalent to canonical Zeckendorf index lists. IsZeckendorfRep requires every occupied Fibonacci index to be at least two and consecutive occupied indices to differ by at least two; its inverse sums the selected Fibonacci numbers. Thus the equivalence states existence and uniqueness of the binary, nonadjacent W-digit representation, including the empty representation of zero.

`D5/S0/Conventions/WDigits` fixes the zero-based weights `W(k)=F(k+2)`, hence `1,2,3,5,...`. A digit string is represented by its occupied Fibonacci indices.

The module delegates the canonical algorithm and proof to mathlib's Zeckendorf development. It exposes the three repository-facing facts: indices are nonadjacent, decoding returns the original natural number, and no other canonical list decodes to the same value.

## References

- Truth anchor: `D5/S0/Conventions/WDigits.wEncoding`
- Narrative reference: [D5/S0/Conventions/WDigits](WDigits.md)
