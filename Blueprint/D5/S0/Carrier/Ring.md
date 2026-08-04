# Golden Integer Ring

## Abstract

Golden integers use integral coordinates with the quadratic relation built into multiplication.

`D5/S0/Carrier/Ring` represents each element of `Z[phi]` by its unique integral coordinates `a + b*phi`. Multiplication reduces `phi^2` to `phi + 1`, so the defining quadratic relation is part of computation rather than an added axiom.

The map to mathlib's `Zsqrtd 5` stores twice the algebraic integer: `a + b*phi` becomes `(2a+b) + b*sqrt(5)`. Consequently it is additive, injective, and its multiplication law carries an explicit factor of two; it is deliberately not mislabeled as a ring homomorphism.

## References

- Narrative reference: [D5/S0/Carrier/Ring](Ring.md)
