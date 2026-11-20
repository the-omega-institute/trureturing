# Two-defect width-4 king arrays

## Abstract

Four-colour width-4 king arrays with exactly two monochromatic bonds.

The exact-budget transfer records successor multiplicities and first-row weights. The list-to-grid identity and colour normalization express its labelled count as 24 times the canonical count. A linear relation among the forward vectors then gives the recurrence.

**Theorem 1.1 (The width-4 six-term recurrence).**

$$\forall (n: \operatorname{Nat}), ((12 \le n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(n, 4\right)\right) = ((((((9) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right), 4\right)\right))) - ((33) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 2\right), 4\right)\right)))) + ((63) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 3\right), 4\right)\right)))) - ((66) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 4\right), 4\right)\right)))) + ((36) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 5\right), 4\right)\right)))) - ((8) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 6\right), 4\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229751.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

The literal count T(n,4) includes exactly two monochromatic horizontal, vertical, diagonal or antidiagonal bonds and uses row-major colour introduction. The 19-class exact-budget transfer counts labelled colourings. For n >= 2, KingTwoGrid.labelled_eq_twentyFour divides by 24; three occurring colours suffice for the free permutation action. The recurrence holds for every n >= 12, including the threshold.

The twelve-row forward table satisfies W(11)=-8W(5)+36W(6)-66W(7)+63W(8)-33W(9)+9W(10). DefectTransfer.forward_shift propagates this integer relation to every later height. The GridBridge identifies the row-list cost with the literal grid edge count. These are finite combinatorial states of the four-state Potts antiferromagnet at exactly two unsatisfied bonds; no empirical physical claim is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229751.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid](KingTwoGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge](TwoDefectStrips/GridBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Certificate](TwoDefectStrips/Width4/Certificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data](TwoDefectStrips/Width4/Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Forward](TwoDefectStrips/Width4/Forward.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/Topology/QuandleMarkovColoring](../../../Topology/QuandleMarkovColoring.md)
