# Five-column strip colourings

## Abstract

Exact-budget diagonal and antidiagonal arrays.

**Definition 1.1 (cl).**

$$\forall p: (\operatorname{\mathit{Fin}}\left(5\right)) \to (\operatorname{\mathit{Fin}}\left(3\right)), (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{cl}}\left(p, d\right): \operatorname{\mathit{Fin}}\left(24\right)) = (\operatorname{\mathit{if}} (d = 2) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(16, \operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{boundary}}\left(p\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(8, \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{cl}}\left(p, d\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

The residual budget selects the new leading sector or the retained lower-budget sectors. Fin.castAdd preserves the index value in a larger finite type; Fin.natAdd adds its stated offset to the index value.

**Definition 1.2 (costTwo).**

$$(\operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{costTwo}}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(8\right), \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.costTwo` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

This eight by eight integer table is pinned by HardinA229682StripCertificate.two_counts: its entries count successors with exactly 2 equal-colour bonds.

**Definition 1.3 (T).**

$$(\operatorname{\mathit{HardinA229682StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(24\right), \operatorname{\mathit{Fin}}\left(24\right), \mathit{Int}\right)) = \operatorname{\mathit{Matrix}}.\operatorname{\mathit{reindex}}\left((\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(16\right)\right), \operatorname{\mathit{Fin}}\left(24\right)\right)), (\operatorname{\mathit{finSumFinEquiv}}: \operatorname{\mathit{Equiv}}\left(\operatorname{\mathit{Sum}}\left(\operatorname{\mathit{Fin}}\left(8\right), \operatorname{\mathit{Fin}}\left(16\right)\right), \operatorname{\mathit{Fin}}\left(24\right)\right)), \operatorname{\mathit{Matrix}}.\operatorname{\mathit{fromBlocks}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{T}, \lambda i: \operatorname{\mathit{Fin}}\left(8\right) \mapsto (\operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{costOne}}\left(i\right), \operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{costTwo}}\left(i\right)\right)), (0: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(16\right), \operatorname{\mathit{Fin}}\left(8\right), \mathit{Int}\right)), \operatorname{\mathit{HardinA229507StripData}}.\operatorname{T}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

The bottom-right 16 by 16 block is HardinA229507StripData.T. The leading sector uses the original zero-cost transfer and the additional exact-cost matrices.

**Definition 1.4 (initial).**

$$\operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{initial}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(\operatorname{\mathit{HardinA203980StripData}}.\operatorname{\mathit{initial}}, (0: (\operatorname{\mathit{Fin}}\left(16\right)) \to (\mathit{Int}))\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

All first rows begin in the largest residual budget.

**Definition 1.5 (terminal).**

$$\operatorname{\mathit{HardinA229682StripData}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left((0: (\operatorname{\mathit{Fin}}\left(8\right)) \to (\mathit{Int})), \operatorname{\mathit{HardinA229507StripData}}.\operatorname{\mathit{terminal}}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229682: canonical diagonal and antidiagonal strip colourings*. URL: <https://oeis.org/A229682>.

*Commentary.*

Acceptance requires the residual budget to be zero.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.costTwo`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229682StripData.terminal`
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA203980StripData](HardinA203980StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/DiagonalStripDefects/HardinA229507StripData](HardinA229507StripData.md)
