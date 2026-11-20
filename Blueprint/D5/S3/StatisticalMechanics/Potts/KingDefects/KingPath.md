# One-defect king colourings: KingPath

## Abstract

Finite colourings with exactly one monochromatic king bond.

**Definition 1.1 (Recursive adjacent-equality cost).**

$$\forall (C: \operatorname{Type}), ([\operatorname{DecidableEq}\left(C\right)], (\forall (p: C), (\forall (f: \operatorname{Fin}\left(0\right) \to C), (\operatorname{errors}\left(p, f\right) = 0))) \land (\forall (n: \operatorname{Nat}), (\forall (p: C), (\forall (c: C), (\forall (f: \operatorname{Fin}\left(n\right) \to C), (\operatorname{errors}\left(p, \operatorname{Fin}.\operatorname{cons}\left(c, f\right)\right) = ((\operatorname{if} (p = c) \operatorname{then} 1 \operatorname{else} 0)) + (\operatorname{errors}\left(c, f\right))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.errors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting from the preceding colour p, the recursion adds one exactly when the next colour equals p.

**Definition 1.2 (The adjacent-equality sum).**

$$\forall (C: \operatorname{Type}), ([\operatorname{DecidableEq}\left(C\right)], \forall (n: \operatorname{Nat}), (\forall (f: \operatorname{Fin}\left(n\right) \to C), (\operatorname{bad}\left(f\right) = \sum_{(i: \operatorname{Fin}\left((n) - (1)\right))} (\operatorname{if} (f\left(\operatorname{KingGrid}.\operatorname{lo}\left(i\right)\right) = f\left(\operatorname{KingGrid}.\operatorname{hi}\left(i\right)\right)) \operatorname{then} 1 \operatorname{else} 0))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.bad` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each consecutive pair contributes its equality indicator; the sum is zero for words of length at most one.

**Theorem 1.3 (The sum equals the recursive cost).**

$$\forall (C: \operatorname{Type}), ([\operatorname{DecidableEq}\left(C\right)], \forall (n: \operatorname{Nat}), (\forall (f: \operatorname{Fin}\left((n) + (1)\right) \to C), (\operatorname{bad}\left(f\right) = \operatorname{errors}\left(f\left(0\right), \operatorname{Fin}.\operatorname{tail}\left(f\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.errors_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary colour type with decidable equality, the adjacent-equality sum equals the recursion started at the first letter. The two-defect path bridge reuses this original correspondence.

**Theorem 1.4 (Canonical words and canonical one-column grids).**

$$\forall (n: \operatorname{Nat}), (\forall (f: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(4\right)), (\operatorname{KingGrid}.\operatorname{normal}\left((\lambda (p: \operatorname{KingGrid}.\operatorname{Cell}\left(n, 1\right)) \mapsto \operatorname{f}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right))\right) \Leftrightarrow \operatorname{HardinA233177Canonical}.\operatorname{Canonical}\left(f\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.normal_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row-major order on a one-column grid agrees with the order of its word positions, so the two restricted-growth conditions are equivalent.

**Theorem 1.5 (The width-one count for at least three cells).**

$$\forall (n: \operatorname{Nat}), ((3 \le n) \Rightarrow ((54) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingGrid}.\operatorname{T}\left(n, 1\right)\right)) = (((\operatorname{Int}.\operatorname{ofNat}\left(n\right)) - (1)) \cdot (((3: \operatorname{Int}))^{n})) + ((27) \cdot ((\operatorname{Int}.\operatorname{ofNat}\left(n\right)) - (1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.width_one_large` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin (2013). *T(n,k) = number of defective 4-colorings of an n X k 0..3 array connected horizontally, vertically, diagonally and antidiagonally with exactly one mistake, and colors introduced in row-major 0..3 order.*. URL: <https://oeis.org/A229578>.

*Commentary.*

A one-column array is a word with exactly one equal adjacent pair. Burnside counting for permutations of four colours gives the formula for every word of length at least three.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.bad`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.errors`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.errors_eq`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.normal_path`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.width_one_large`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
