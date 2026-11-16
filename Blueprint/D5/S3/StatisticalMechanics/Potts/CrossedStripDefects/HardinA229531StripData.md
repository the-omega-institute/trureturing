# Width-five HDA transfer

## Abstract

Exact width-five HDA transfer.

**Definition 1.1 (Actual rows).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Row`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

Row is the function type Fin 5 to Fin 3. Its 243 values are the actual labelled rows.

**Definition 1.2 (Horizontal bonds).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.horizontal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.horizontal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The horizontal bond set is HardinA229583StripData.horizontal, containing the four adjacent pairs in Fin 5.

**Definition 1.3 (Crossed bonds).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.between`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.between` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The inter-row bond set is the union of HardinA229583StripData.antidiagonal with its coordinate-swapped image, containing both diagonals for each adjacent column pair.

**Definition 1.4 (Valid residual states).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Valid`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

Valid p d means that d is at most one and the internal horizontal defect count of p is at most one minus d.

**Definition 1.5 (Finite state decision).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.decidableValid`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.decidableValid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The instance decides the conjunction defining Valid on an actual row and natural residual budget.

**Definition 1.6 (The class map).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.cl`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The map Row times Nat to Fin 20 identifies global colour permutations and reflection. Proper rows use HardinA233126SquareStrip.boundaryClass at Seen=(true,true); defective rows use their full equality pattern. The transition_counts theorems pin the class transfer for every valid state.

**Definition 1.7 (The transfer matrix).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.T`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

T is an integer matrix indexed by Fin 20 on both axes. Its proper-row diagonal subblocks call HardinA233171DiagonalStrip.transfer at indices one through six and divide by 32. The division removes the two lifts per colour in each of five cells after Seen is saturated. Every entry is pinned to the actual three-colour successor sum by HardinA229531StripClasses.transition_counts.

**Definition 1.8 (Initial distribution).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.initial`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The vector Fin 20 to Int counts first rows by their exact residual budget and class. HardinA229531Strip.finite_certificate verifies these weights.

**Definition 1.9 (Terminal acceptance).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.terminal`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

The vector Fin 20 to Int is one exactly at zero-residual classes and zero otherwise; HardinA229531Strip.finite_certificate checks this for all valid rows.

**Definition 1.10 (Forward weights).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.W`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229531: exact-defect canonical three-colour arrays*. URL: <https://oeis.org/A229531>.

*Commentary.*

W has type Fin 14 to Fin 20 to Int. Its fourteen rows are the initial vector followed by thirteen right multiplications by T. HardinA229531Strip.finite_certificate pins those identities and the order-twelve polynomial relation.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Row`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.between`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.decidableValid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.horizontal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229531StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233171DiagonalStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229583StripData](../StripDefects/HardinA229583StripData.md)
