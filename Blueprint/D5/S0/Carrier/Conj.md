# Golden Conjugation

## Abstract

Golden conjugation is an involutive ring equivalence with integral trace.

`D5/S0/Carrier/Conj` sends `a + b*phi` to `(a+b) - b*phi`, equivalently replacing `phi` by `1-phi`. The implementation proves that this map preserves addition and multiplication and is its own inverse, then packages those facts as a ring equivalence.

The trace is `2a+b`, and the module checks that doubled coordinates commute exactly with mathlib's star operation on `Zsqrtd 5`.

## References

- Dependency: [D5/S0/Carrier/Ring](Ring.md)
