# W-Digit Convention

## Abstract

W digits use shifted Fibonacci weights and the canonical Zeckendorf representation.

`D5/S0/Conventions/WDigits` fixes the zero-based weights `W(k)=F(k+2)`, hence `1,2,3,5,...`. A digit string is represented by its occupied Fibonacci indices.

The module delegates the canonical algorithm and proof to mathlib's Zeckendorf development. It exposes the three repository-facing facts: indices are nonadjacent, decoding returns the original natural number, and no other canonical list decodes to the same value.

## References

- Narrative reference: [D5/S0/Conventions/WDigits](WDigits.md)
