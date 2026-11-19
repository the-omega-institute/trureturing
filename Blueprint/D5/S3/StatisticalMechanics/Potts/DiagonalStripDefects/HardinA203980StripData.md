# Diagonal strip colourings

## Abstract

Five-column diagonal and antidiagonal strip counts.

**Definition 1.1 (Row).**

$$\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{Row}} = (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

An actual labelled row is a function from Fin 5 to Fin 3.

**Definition 1.2 (horizontal).**

$$(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{horizontal}}: \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(5\right), \operatorname{\mathit{Fin}}\left(5\right)\right)\right)) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The within-row bond set is empty.

**Definition 1.3 (between).**

$$(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{between}}: \operatorname{\mathit{Finset}}\left(\operatorname{\mathit{Prod}}\left(\operatorname{\mathit{Fin}}\left(5\right), \operatorname{\mathit{Fin}}\left(5\right)\right)\right)) = \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((0, 1), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((1, 0), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((1, 2), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((2, 1), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((2, 3), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((3, 2), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((3, 4), \operatorname{\mathit{Finset}}.\operatorname{\mathit{insert}}\left((4, 3), \operatorname{\mathit{Finset}}.\operatorname{\mathit{empty}}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The eight ordered column pairs join adjacent rows diagonally and antidiagonally. No bond joins equal column indices.

**Definition 1.4 (boundary).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), ((\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right): \operatorname{\mathit{Fin}}\left(8\right)) = (\operatorname{\mathit{if}} ((p\left(0\right) = p\left(2\right)) \land (p\left(2\right) = p\left(4\right))) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 0 \operatorname{\mathit{else}} 1) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(0\right) = p\left(4\right)) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 2 \operatorname{\mathit{else}} 3) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} ((p\left(0\right) = p\left(2\right)) \lor (p\left(2\right) = p\left(4\right))) \operatorname{\mathit{then}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 4 \operatorname{\mathit{else}} 5) \operatorname{\mathit{else}} (\operatorname{\mathit{if}} (p\left(1\right) = p\left(3\right)) \operatorname{\mathit{then}} 6 \operatorname{\mathit{else}} 7)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The eight cases depend on equality among columns zero, two and four and equality between columns one and three. A reflection identifies the two adjacent equality cases.

**Definition 1.5 (representatives).**

$$(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{representatives}}: (\operatorname{\mathit{Fin}}\left(8\right)) \to ((\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.representatives` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

This table has type Fin 8 to Row, with eight rows of five colours: [[0, 0, 0, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 1, 0], [0, 0, 0, 0, 1], [0, 0, 0, 1, 1], [0, 0, 1, 0, 2], [0, 0, 1, 1, 2]]. DiagonalSymmetry.lift_counts establishes that these representatives determine successor counts for every actual row.

**Definition 1.6 (T).**

$$(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right), \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The eight by eight integer table is pinned by HardinA203980StripCertificate.counts: entry i,j is the number of cost-zero successors in class j from the representative of class i.

**Definition 1.7 (initial).**

$$(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{initial}}: (\operatorname{\mathit{Fin}}\left(8\right)) \to (\mathit{Int}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

The eight integer entries are [9, 18, 18, 36, 36, 72, 18, 36]. HardinA203980StripCertificate.initial_counts pins them as the distribution of all 243 labelled rows.

**Definition 1.8 (terminal).**

$$\forall j: \operatorname{\mathit{Fin}}\left(8\right), (\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{terminal}}\left(j\right) = (1: \mathit{Int}))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2012). *OEIS A203980: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A203980>.

*Commentary.*

Each of the eight terminal integer weights is one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.boundary`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.representatives`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData.terminal`
