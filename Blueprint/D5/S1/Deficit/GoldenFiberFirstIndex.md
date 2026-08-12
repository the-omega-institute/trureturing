# Equivalent Floor Formulas for the First Golden Fiber Index

## Abstract

The corrected and compressed floor formulas for the first golden fiber index agree.

**Theorem 1.1 (The two first-index floor formulas agree).**

$$\forall a \in \mathbb{N},\ 1 \leq a \implies \lfloor a\varphi - \varphi^{2}\rfloor + 1 = \lfloor(a - 1)\varphi\rfloor$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/GoldenFiberFirstIndex.golden_fiber_first_index_forms_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural fiber label, the floor of a times the golden ratio minus its square, followed by adding one, equals the floor of a minus one times the golden ratio.

The proof rewrites the square of the golden ratio as the golden ratio plus one, converts positivity into the exact natural subtraction cast, and then applies the library floor-minus-one identity. The pinned library contains those component identities but no declaration of their assembled first-index equality.

This is an honest partial closure of the source corollary. It covers only the equality between its corrected and compressed first-index formulas; the Beatty fiber criterion, image statement, capacity statement, and the joint coordinate-family claim remain unresolved.

## References

- Truth anchor: `D5/S1/Deficit/GoldenFiberFirstIndex.golden_fiber_first_index_forms_eq`
