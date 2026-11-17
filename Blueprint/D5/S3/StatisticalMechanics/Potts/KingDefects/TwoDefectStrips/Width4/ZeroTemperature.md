# Complementary-pair fibres

## Abstract

The proper zero-budget transfer descends from the signed saturated certificate.

**Theorem 1.1 (The zero-budget transfer).**

$$\forall (p: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary}), (((\operatorname{HardinA233164KingStrip}.\operatorname{proper}\left(p\right)) \lor (\operatorname{Data}.\operatorname{cl}\left(p, 0\right) = 14)) \Rightarrow (\forall (s: \operatorname{Fin}\left(19\right)), (\sum_{(r: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary})} ((\operatorname{if} ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)) \le 0) \land (\operatorname{Data}.\operatorname{cl}\left(r, (0) - ((\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{between}, p, r\right)) + (\operatorname{DefectTransfer}.\operatorname{bondDefects}\left(\operatorname{Data}.\operatorname{horizontal}, r, r\right)))\right) = s) \operatorname{then} (1: \operatorname{Int}) \operatorname{else} (0: \operatorname{Int}))) = \operatorname{Data}.\operatorname{T}\left(\operatorname{Data}.\operatorname{cl}\left(p, 0\right), s\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/ZeroTemperature.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The map beta sends complementary signed colours to the same four-colour label. Every raw boundary has exactly 16 signed preimages, with two independent choices per column. SignedFibres.sum_beta gives the weighted identity with factor 2^4. The signed row predicate is equivalent to zero defects after applying the map. The owner saturated_certificate preserves the productive boundary type and gives the signed rate. The class containing alternating ABAB also contains ABBA, whose two middle entries coincide. Replacing ABBA by ABAB preserves the zero-defect next-row constraint, and both source rows have class 14. Class correspondence transports kind to the two zero-budget classes, so dividing the signed rate by 16 gives the displayed entry. At width 4, the two signed rates are 32 and 16, hence the raw rates are two and one. All sums and matrix entries are integers; the subtraction inside Data.cl is natural subtraction.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/ZeroTemperature.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233196Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres](../SignedFibres.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data](Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229582Strip](../../../StripDefects/HardinA229582Strip.md)
