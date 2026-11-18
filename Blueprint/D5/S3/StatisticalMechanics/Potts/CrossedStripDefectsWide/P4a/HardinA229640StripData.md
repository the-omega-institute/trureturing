# HardinA229640StripData

## Abstract

Four-row two-defect HDA strips.

The budget-two class map and endpoint vectors are those of A229697. At every budget other than two the class map appends fourteen to the saturated one-defect class. The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index.

**Definition 1.1 (cl).**

$$\forall (p: \operatorname{Fin}\left(4\right) \to \operatorname{Fin}\left(3\right)), (\forall (d: \operatorname{Nat}), (\operatorname{HardinA229640StripData}.\operatorname{cl}\left(p, d\right) = (\operatorname{if} (d = 2) \operatorname{then} \operatorname{HardinA229697StripData}.\operatorname{cl}\left(p, 2\right) \operatorname{else} \operatorname{Fin}.\operatorname{natAdd}\left(14, \operatorname{HardinA229537StripData}.\operatorname{cl}\left(p, d\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The budget-two class map and endpoint vectors are those of A229697. At every budget other than two the class map appends fourteen to the saturated one-defect class. The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index.

**Definition 1.2 (T).**

$$\operatorname{HardinA229640StripData}.\operatorname{T} = \operatorname{Matrix}.\operatorname{reindex}\left((\operatorname{finSumFinEquiv}: \operatorname{Equiv}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(28\right)\right), \operatorname{Fin}\left(42\right)\right)), (\operatorname{finSumFinEquiv}: \operatorname{Equiv}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(28\right)\right), \operatorname{Fin}\left(42\right)\right)), \operatorname{Matrix}.\operatorname{fromBlocks}\left(\operatorname{HardinA233177PairTransfer}.\operatorname{Q}, (\lambda (i: \operatorname{Fin}\left(14\right))\mapsto (\operatorname{Fin}.\operatorname{append}\left(\operatorname{Matrix}.\operatorname{submatrix}\left(\operatorname{HardinA229537StripData}.\operatorname{T}, (\lambda (i: \operatorname{Fin}\left(14\right))\mapsto (\operatorname{Fin}.\operatorname{castAdd}\left(14, i\right))), (\lambda (j: \operatorname{Fin}\left(14\right))\mapsto (\operatorname{Fin}.\operatorname{natAdd}\left(14, j\right))), i\right), (\begin{pmatrix}0&2&0&0&2&0&0&2&0&2&4&0&2&2\\1&1&1&1&2&1&0&1&0&2&1&1&1&1\\0&1&2&1&2&2&1&2&1&1&0&0&1&1\\0&1&1&1&2&1&2&1&2&1&0&1&1&2\\1&2&2&2&2&1&1&1&1&1&1&1&1&1\\0&1&2&1&1&2&1&1&1&1&0&0&2&2\\0&0&1&2&1&1&2&1&2&0&2&1&1&1\\1&1&2&1&1&1&1&1&1&1&1&1&1&1\\0&0&1&2&1&1&2&1&3&0&2&0&1&1\\1&2&1&1&1&1&0&1&0&1&1&1&1&2\\2&1&0&0&1&0&2&1&2&1&2&1&1&1\\0&1&0&1&1&0&1&1&0&1&1&0&1&1\\1&1&1&1&1&2&1&1&1&1&1&1&1&1\\1&1&1&2&1&2&1&1&1&2&1&1&1&2\end{pmatrix}: \operatorname{Matrix}\left(\operatorname{Fin}\left(14\right), \operatorname{Fin}\left(14\right), \operatorname{Int}\right))\left(i\right)\right))), (0: \operatorname{Matrix}\left(\operatorname{Fin}\left(28\right), \operatorname{Fin}\left(14\right), \operatorname{Int}\right)), \operatorname{HardinA229537StripData}.\operatorname{T}\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The budget-two class map and endpoint vectors are those of A229697. At every budget other than two the class map appends fourteen to the saturated one-defect class. The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index.

**Definition 1.3 (initial).**

$$\operatorname{HardinA229640StripData}.\operatorname{initial} = \operatorname{HardinA229697StripData}.\operatorname{initial}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The budget-two class map and endpoint vectors are those of A229697. At every budget other than two the class map appends fourteen to the saturated one-defect class. The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index.

**Definition 1.4 (terminal).**

$$\operatorname{HardinA229640StripData}.\operatorname{terminal} = \operatorname{HardinA229697StripData}.\operatorname{terminal}$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229640: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229640>.

*Commentary.*

The budget-two class map and endpoint vectors are those of A229697. At every budget other than two the class map appends fourteen to the saturated one-defect class. The first fourteen coordinates have two remaining defects. The trailing twenty-eight coordinates are exactly the one-defect transfer. The upper block consists of its one-defect block followed by the literal two-defect table. Each table entry counts next columns with exactly two monochromatic bonds. The submatrix selects rows zero through thirteen and columns fourteen through twenty-seven of the one-defect matrix. Fin.append concatenates the two fourteen-coordinate vectors; Fin.natAdd adds fourteen to an index.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229640StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P4a/HardinA229537StripData](HardinA229537StripData.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData](../../StripDefectsTwo/HardinA229697StripData.md)
