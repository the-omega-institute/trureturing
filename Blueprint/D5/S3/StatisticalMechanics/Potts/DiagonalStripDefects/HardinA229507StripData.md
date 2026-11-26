# Five-column strip colourings

## Abstract

Exact-budget diagonal and antidiagonal arrays.

**Definition 1.1 (cl).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{cl}}\left(p, d\right): \operatorname{\mathit{Fin}}\left(16\right)) = (\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(8, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(8, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

The residual budget selects the new leading sector or the retained lower-budget sectors. Fin.castAdd preserves the index value in a larger finite type; Fin.natAdd adds its stated offset to the index value.

**Definition 1.2 (costOne).**

$$(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{costOne}}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right), \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.costOne` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

This eight by eight integer table is pinned by HardinA229507StripCertificate.one_counts: its entries count successors with exactly 1 equal-colour bonds.

**Definition 1.3 (T).**

$$(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(16\right), \operatorname{\mathit{Fin}}\left(16\right), \mathit{Int}\right)) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{reindex}}\left((\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right)\right), \operatorname{\mathit{Fin}}\left(16\right)\right)), (\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right)\right), \operatorname{\mathit{Fin}}\left(16\right)\right)), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{fromBlocks}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}, \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{costOne}}, (0: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right), \mathit{Int}\right)), \operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

The bottom-right 8 by 8 block is HardinA203980StripData.T. The leading sector uses the original zero-cost transfer and the additional exact-cost matrices.

**Definition 1.4 (initial).**

$$\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{initial}}, (0: (\operatorname{\mathit{Fin}}\left(8\right)) \to (\mathit{Int}))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

All first rows begin in the largest residual budget.

**Definition 1.5 (terminal).**

$$\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((0: (\operatorname{\mathit{Fin}}\left(8\right)) \to (\mathit{Int})), \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{terminal}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229507: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229507>.

*Commentary.*

Acceptance requires the residual budget to be zero.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.costOne`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
