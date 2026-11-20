# Two-defect king colourings

## Abstract

Literal canonical two-defect king colourings.

**Definition 1.1 (Exactly two equal-colour bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{KingTwoGrid}.\operatorname{TwoDefect}\left(f\right)) \Leftrightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)) \mapsto \operatorname{KingGrid}.\operatorname{mono}\left(f, e\right)), \operatorname{Finset}.\operatorname{univ}\left(\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)\right)\right)\right) = 2))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.TwoDefect` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

The filter counts the four disjoint king-edge constructors, with no orientation duplication.

**Definition 1.2 (Canonical two-defect count).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingTwoGrid}.\operatorname{T}\left(n, k\right) = \operatorname{Nat}.\operatorname{card}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right)) // ((\operatorname{KingTwoGrid}.\operatorname{TwoDefect}\left(f\right)) \land (\operatorname{KingGrid}.\operatorname{normal}\left(f\right)))\}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.T` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

Row-major restricted growth selects one representative of every colour orbit.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.TwoDefect`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
