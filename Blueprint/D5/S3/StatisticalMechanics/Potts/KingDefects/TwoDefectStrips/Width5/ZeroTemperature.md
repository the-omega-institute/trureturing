# Width-five proper successors by restriction

## Abstract

The width-five proper block is the reflected-column restriction of the frozen width-six owner.

**Definition 1.1 (The reflected-column extension).**

$$\forall (p: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), (\operatorname{extend}\left(p\right) = ![p\left(0\right), p\left(1\right), p\left(2\right), p\left(3\right), p\left(4\right), p\left(3\right)])$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.extend` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

A width-five row is extended by reflecting its penultimate column into the sixth column. The new adjacent square reflects the preceding square, so it adds no new inequality.

**Definition 1.2 (The width-five zero-defect relation).**

$$\forall (p: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (r: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{raw5}\left(p, r\right)) \Leftrightarrow ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{horizontal}, r, r\right)) = 0)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw5` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The raw successor relation records zero between-row and horizontal defects for width five.

**Theorem 1.3 (Properness is preserved by extension).**

$$\forall (p: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width6}.\operatorname{Data}.\operatorname{horizontal}, \operatorname{extend}\left(p\right), \operatorname{extend}\left(p\right)\right) = 0) \Leftrightarrow (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{horizontal}, p, p\right) = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.proper_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The reflected extension has no horizontal defects exactly when the original width-five row has none.

**Theorem 1.4 (Raw successors are preserved by extension).**

$$\forall (p: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (r: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{Width6}.\operatorname{ZeroTemperature}.\operatorname{raw}\left(\operatorname{extend}\left(p\right), \operatorname{extend}\left(r\right)\right)) \Leftrightarrow (\operatorname{raw5}\left(p, r\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

The width-six owner relation on reflected extensions is equivalent to the width-five raw relation.

**Theorem 1.5 (The restricted owner image).**

$$\forall (p: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), (\forall (r: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{horizontal}, p, p\right) = 0) \Rightarrow ((\operatorname{raw5}\left(p, r\right)) \Leftrightarrow (\exists (v: \operatorname{Fin}\left(4\right)), ((v \in \operatorname{HardinA233166KingStrip}.\operatorname{offsetChoices}\left(\operatorname{Width6}.\operatorname{ZeroTemperature}.\operatorname{offsets}\left(\operatorname{extend}\left(p\right)\right)\right)) \land (r = (\lambda (j: \operatorname{Fin}\left(5\right)) \mapsto \operatorname{Fin}.\operatorname{xor}\left(v, p\left(j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/ZeroTemperature.raw_iff_owner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233166: normalized eight-colour six-column king strips*. URL: <https://oeis.org/A233166>.

*Commentary.*

For every horizontally proper width-five source, every zero-defect successor is the restriction of an owner allowed shift, and every such restriction is a successor. The shift is recovered uniquely as r(0) xor p(0), giving fibre multiplicity one.

**Theorem 1.6 (The zero-temperature transfer row).**

$$\forall (p: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right))), ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{horizontal}, p, p\right) = 0) \Rightarrow (\forall (s: \operatorname{Fin}\left(43\right)), (\sum_{(r: (\operatorname{Fin}\left(5\right)) \to (\operatorname{Fin}\left(4\right)))} ((\operatorname{if} (((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{horizontal}, r, r\right)) \le 0) \land (\operatorname{Width5}.\operatorname{Data}.\operatorname{cl}\left(r, (0) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{horizontal}, r, r\right)))\right) = s)) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{Width5}.\operatorname{Data}.\operatorname{T}\left(\operatorname{Width5}.\operatorname{Data}.\operatorname{cl}\left(p, 0\right), s\right))))$$

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
