# Width-five proper successors by restriction

## Abstract

The width-five proper block is the reflected-column restriction of the frozen width-six owner.

**Definition 1.1 (The reflected-column extension).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.extend`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.extend` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

A width-five row is extended by reflecting its penultimate column into the sixth column. The new adjacent square reflects the preceding square, so it adds no new inequality.

**Definition 1.2 (The width-five zero-defect relation).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw5`

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw5` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The raw successor relation records zero between-row and horizontal defects for width five.

**Theorem 1.3 (Properness is preserved by extension).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.proper_extend`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.proper_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The reflected extension has no horizontal defects exactly when the original width-five row has none.

**Theorem 1.4 (Raw successors are preserved by extension).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_extend`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The width-six owner relation on reflected extensions is equivalent to the width-five raw relation.

**Theorem 1.5 (The restricted owner image).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_iff_owner`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_iff_owner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

Every width-five zero-defect successor is the restriction of an owner allowed shift, and every such restriction is a successor. The shift is recovered uniquely as r(0) xor p(0), giving fibre multiplicity one.

**Theorem 1.6 (The zero-temperature transfer row).**

Lean statement: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.transition_counts`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

For every horizontally proper width-five source and every class column, the zero-budget successor sum equals the width-five transfer row.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.extend`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.proper_extend`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw5`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_extend`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_iff_owner`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data](Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width6/ZeroTemperature](../Width6/ZeroTemperature.md)
