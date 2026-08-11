# Zolotarev Selector Congruence

## Abstract

The inverse-residue congruence factors the selector Jacobi symbol.

**Theorem 1.1 (The inverse-residue congruence factors the selector symbol).**

$$\forall b, g, d: \mathbb{Z},\ 4bg \equiv -1 (\operatorname{mod} d) \Rightarrow\ (\frac{2g}{\lvert d \rvert})=(\frac{2}{\lvert d \rvert})(\frac{-1}{\lvert d \rvert})(\frac{b}{\lvert d \rvert}).$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/ZolotarevSelector.zolotarev_selector_congruence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Zolotarev inverse-residue congruence 4bg = -1 modulo d makes 2g and -2b inverse residues, so their Jacobi symbols agree and the selector symbol at 2g factors into the three displayed Jacobi symbols over the absolute modulus. The factorization side reuses the frozen selector-numerator theorem; the transport side carries the congruence through the natural-absolute-value reduction.

An explicit witness at b = g = 1, d = 5 exercises the congruence with a nontrivial value of the two-symbol, so the statement is not vacuously satisfied.

## References

- Truth anchor: `D5/S1/Phase/Interference/ZolotarevSelector.zolotarev_selector_congruence`
- Dependency: [D5/S1/Phase/SeatTowerConsequences](../SeatTowerConsequences.md)
