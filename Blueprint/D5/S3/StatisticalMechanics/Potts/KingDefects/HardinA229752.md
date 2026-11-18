# Two-defect width-five king arrays

## Abstract

Four-colour width-five king arrays with exactly two monochromatic bonds.

The result uses the new defect-domain successor and initial certificates, the list-to-grid bridge and the colour-normalization proof. Inlining these dependencies retains their mathematical content; the subsequent Krylov and integer calculations normalize the certified table.

**Theorem 1.1 (The width-five six-term recurrence).**

$$\forall (n: \operatorname{Nat}), ((12 \le n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(n, 5\right)\right) = ((((((9) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right), 5\right)\right))) - ((33) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 2\right), 5\right)\right)))) + ((63) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 3\right), 5\right)\right)))) - ((66) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 4\right), 5\right)\right)))) + ((36) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 5\right), 5\right)\right)))) - ((8) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 6\right), 5\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229752` (proved) by `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229752","declaration_gid":"D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229752: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229752>.

*Commentary.*

The literal count T(n,5) includes exactly two monochromatic horizontal, vertical, diagonal or antidiagonal bonds and uses row-major colour introduction. The 43-class exact-budget transfer counts labelled colourings. For n >= 2, KingTwoGrid.labelled_eq_twentyFour divides by 24; three occurring colours suffice for the free permutation action. The recurrence holds for every n >= 12, including the threshold.

The twelve-row forward table satisfies W(11)=-8W(5)+36W(6)-66W(7)+63W(8)-33W(9)+9W(10). DefectTransfer.forward_shift propagates this integer relation to every later height. The GridBridge identifies the row-list cost with the literal grid edge count. These are finite combinatorial states of the four-state Potts antiferromagnet at exactly two unsatisfied bonds; no empirical physical claim is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229752.result`
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid](KingTwoGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge](TwoDefectStrips/GridBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Certificate](TwoDefectStrips/Width5/Certificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Data](TwoDefectStrips/Width5/Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width5/Forward](TwoDefectStrips/Width5/Forward.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/Topology/QuandleMarkovColoring](../../../Topology/QuandleMarkovColoring.md)
