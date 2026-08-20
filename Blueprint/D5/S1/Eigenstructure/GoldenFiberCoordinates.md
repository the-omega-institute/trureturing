# Exact Beatty Formulas for Golden Fiber Coordinates

## Abstract

The two golden fiber coordinates have exact Beatty floor formulas.

**Theorem 1.1 (The golden fiber coordinates are Beatty floor differences).**

$$\forall v \in \mathbb{N},\ 1 \leq v \implies a(v)=\lfloor\frac{v+1}{\varphi}\rfloor-\lfloor\frac{v+1}{\varphi^{2}}\rfloor,\quad b(v)=\lfloor\frac{v+1}{\varphi^{2}}\rfloor,\quad a(v)+b(v)=\lfloor\frac{v+1}{\varphi}\rfloor.$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/GoldenFiberCoordinates.golden_fiber_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source coordinates are defined from the Zeckendorf displacement reading by a(v) = 2 S(v) - 3 v and b(v) = 2 v - S(v). For every positive index, both coordinates and their sum are identified with exact floor readings at the inverse golden ratio and its square.

The proof reuses the repository's frozen displacement identity S(v) = floor((v + 1) phi) - 1. Pinned Mathlib supplies the golden-ratio identities, irrationality under nonzero natural scaling, and floor interval bounds. No pinned declaration states the assembled coordinate triple.

This deposit closes only theorem 6.48-prime, clause 2. It does not claim the fiber criterion, capacity statement, support interval, or first-index formula from the surrounding source entries.

## References

- Truth anchor: `D5/S1/Eigenstructure/GoldenFiberCoordinates.golden_fiber_coordinates`
