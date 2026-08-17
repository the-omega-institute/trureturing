# The Square-Root-21 Pell Tower

## Abstract

The norm-one fundamental unit preserves the Pell conic of discriminant 21.

**Theorem 1.1 (The fundamental-unit orbit preserves the Pell equation).**

$$\forall n \in \mathbb{N}, x_n^2-21y_n^2=4$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PellFamilies/SqrtTwentyOnePellTower.sqrt_twenty_one_pell_tower_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Work in the rational quadratic algebra whose generator squares to 21. The seed (5,1) has norm 4, while the fundamental unit (5/2,1/2) has norm 1. If (x n,y n) is the seed multiplied by the n-th power of that unit, then x n squared minus 21 times y n squared is 4 for every natural number n. Its first x n + 1 values are 6, 24, and 111.

Pinned Mathlib defines QuadraticAlgebra.norm as a MonoidHom. The Lean proof computes the two named norms and then applies the existing multiplication and power laws; it does not reprove norm multiplicativity.

This closes only the norm-plus-one Pell-tower clause of remark 27.594. It makes no claim about the SIC reconstruction, numerical restart data, Zauner orbit classes, or torsion spectrum elsewhere in the source atom.

## References

- Truth anchor: `D5/S3/PrimeForms/PellFamilies/SqrtTwentyOnePellTower.sqrt_twenty_one_pell_tower_invariant`
