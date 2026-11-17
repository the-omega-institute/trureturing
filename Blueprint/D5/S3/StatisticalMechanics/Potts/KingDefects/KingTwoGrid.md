# Two-defect colour normalization

## Abstract

Literal two-defect king colourings and colour-orbit normalization.

**Definition 1.1 (Exactly two equal-colour bonds).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\forall (f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{KingTwoGrid}.\operatorname{TwoDefect}\left(f\right)) \Leftrightarrow (\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\lambda (e: \operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)) \mapsto \operatorname{KingGrid}.\operatorname{mono}\left(f, e\right)), \operatorname{Finset}.\operatorname{univ}\left(\operatorname{KingGrid}.\operatorname{Edge}\left(n, k\right)\right)\right)\right) = 2))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.TwoDefect` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

The filter counts the four disjoint king-edge constructors, with no orientation duplication.

**Definition 1.2 (Labelled two-defect count).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingTwoGrid}.\operatorname{L}\left(n, k\right) = \operatorname{Nat}.\operatorname{card}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right)) // (\operatorname{KingTwoGrid}.\operatorname{TwoDefect}\left(f\right))\}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

All four colour names remain distinguished.

**Definition 1.3 (Canonical two-defect count).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), (\operatorname{KingTwoGrid}.\operatorname{T}\left(n, k\right) = \operatorname{Nat}.\operatorname{card}\left(\{f: (\operatorname{KingGrid}.\operatorname{Cell}\left(n, k\right)) \to (\operatorname{Fin}\left(4\right)) // ((\operatorname{KingTwoGrid}.\operatorname{TwoDefect}\left(f\right)) \land (\operatorname{KingGrid}.\operatorname{normal}\left(f\right)))\}\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.T` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

Row-major restricted growth selects one representative of every colour orbit.

**Theorem 1.4 (Twenty-four labelled maps per canonical map).**

$$\forall (n: \operatorname{Nat}), (\forall (k: \operatorname{Nat}), ((2 \le n) \Rightarrow ((2 \le k) \Rightarrow ((n \ne 2 \lor k \ne 2) \Rightarrow (\operatorname{KingTwoGrid}.\operatorname{L}\left(n, k\right) = (24) \cdot (\operatorname{KingTwoGrid}.\operatorname{T}\left(n, k\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.labelled_eq_twentyFour` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

Both dimensions are at least two and the single 2 by 2 block is excluded. Every two-colour 2 by 3 colouring has at least three monochromatic king edges. An injective edge embedding, with transposition for a narrow rectangle, forces three occurring colours. The original KingGrid.canonical_count_three then gives the factor twenty-four. The exceptional 2 by 2 normalization and the global two-defect slot count remain separate obligations.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.L`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.TwoDefect`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.labelled_eq_twentyFour`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
