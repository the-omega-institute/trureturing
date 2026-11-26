# One-defect sectors of the six-column transfer

## Abstract

One-defect sectors of the six-column transfer

**Definition 1.1 (Remaining budget and boundary class).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(6\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{cl}}\left(p, d\right): \operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right)) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} \operatorname{\mathit{Sum}}.\operatorname{\mathit{inr}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Sum}}.\operatorname{\mathit{inl}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{boundary}}\left(p\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The first sector still permits one defect. The second sector has spent its budget.

**Definition 1.2 (The half-strip block with reversed targets).**

$$\forall i: \operatorname{\mathit{Fin}}\left(5\right), (\forall j: \operatorname{\mathit{Fin}}\left(5\right), (\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{halfOne}}\left(i, j\right) = \operatorname{\mathit{HardinA229588Strip}}.\operatorname{T}\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(5, i\right), \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(5, \operatorname{\mathit{Equiv}}.\operatorname{\mathit{swap}}\left(1, 3, j\right)\right)\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.halfOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The row starts with budget 1. The column has zero remaining budget and uses the reversed triple class.

**Definition 1.3 (The exact-one-defect matrix).**

$$\forall i: \operatorname{\mathit{Fin}}\left(15\right), (\forall j: \operatorname{\mathit{Fin}}\left(15\right), (\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{costOne}}\left(i, j\right) = \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classProduct}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfZero}}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{halfOne}}, i, j\right) + \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{classProduct}}\left(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{halfOne}}, \operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{halfZero}}, i, j\right)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.costOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

Each summand counts one allocation of the exact defect cost between the two parity classes.

**Definition 1.4 (One-defect transfer matrix).**

$$(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right), \operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right), \mathit{Int}\right)) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{fromBlocks}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{costOne}}, (0: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right), \mathit{Int}\right)), \operatorname{\mathit{HardinA203981StripData}}.\operatorname{T}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The diagonal blocks preserve the remaining budget. The upper-right block spends it.

**Definition 1.5 (Weights at the first labelled row).**

$$(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{initial}}: (\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right)) \to (\mathit{Int})) = \operatorname{\mathit{Sum}}.\operatorname{\mathit{elim}}\left(\operatorname{\mathit{HardinA203981StripData}}.\operatorname{\mathit{initial}}, (0: (\operatorname{\mathit{Fin}}\left(15\right)) \to (\mathit{Int}))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

The entire budget remains at the first row, with no within-row bonds.

**Definition 1.6 (Weights for exhausting the budget).**

$$(\operatorname{\mathit{HardinA229508StripData}}.\operatorname{\mathit{terminal}}: (\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right)\right)) \to (\mathit{Int})) = \operatorname{\mathit{Sum}}.\operatorname{\mathit{elim}}\left((0: (\operatorname{\mathit{Fin}}\left(15\right)) \to (\mathit{Int})), (1: (\operatorname{\mathit{Fin}}\left(15\right)) \to (\mathit{Int}))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229508: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229508>.

*Commentary.*

Only the zero-remaining-budget sector contributes to the count.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.costOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.halfOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229508StripData.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203981StripData](HardinA203981StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
