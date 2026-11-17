# Width-six proper successors from the zone owner

## Abstract

The frozen six-column proper-colouring owner supplies the zero-temperature block.

**Definition 1.1 (The two-row rectangle).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.twoRows`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.twoRows` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

Two six-column rows form a height-two rectangle, with the source first and the successor second.

**Definition 1.2 (The zero-defect successor relation).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.raw`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.raw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The between-row and target horizontal defect counts both vanish.

**Definition 1.3 (The translated row offsets).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.offsets`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.offsets` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

Offsets translate a proper row by its first entry, producing the owner zone word.

**Theorem 1.4 (The exact allowed-shift image).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.raw_iff_shift`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.raw_iff_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

For a horizontally proper source row, the zero-defect successor rows are exactly the owner offset choices translated across that source. The map sends v to the row j -> v xor p(j); its inverse sends r to r(0) xor p(0). Cancellation gives one successor per allowed shift.

**Theorem 1.5 (The zero-temperature transfer row).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.transition_counts`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

For every horizontally proper source and every class column, the zero-budget successor sum equals the width-six transfer row computed from the allowed shifts. The horizontal properness assumption is essential; rows whose source already has defects use the defect certificates.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.offsets`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.raw`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.raw_iff_shift`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.transition_counts`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature.twoRows`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/Data](Data.md)
