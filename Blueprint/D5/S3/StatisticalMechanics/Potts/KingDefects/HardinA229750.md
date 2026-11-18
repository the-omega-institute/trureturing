# Two-defect width-3 king arrays

## Abstract

Four-colour width-3 king arrays with exactly two monochromatic bonds.

The result uses the new defect-domain successor and initial certificates, the list-to-grid bridge and the colour-normalization proof. Inlining these dependencies retains their mathematical content; the subsequent Krylov and integer calculations normalize the certified table.

**Theorem 1.1 (The width-3 six-term recurrence).**

$$\forall (n: \operatorname{Nat}), ((9 \le n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(n, 3\right)\right) = ((((((9) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right), 3\right)\right))) - ((33) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 2\right), 3\right)\right)))) + ((63) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 3\right), 3\right)\right)))) - ((66) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 4\right), 3\right)\right)))) + ((36) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 5\right), 3\right)\right)))) - ((8) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 6\right), 3\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin229750` (proved) by `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin229750","declaration_gid":"D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The literal count T(n,3) includes exactly two monochromatic horizontal, vertical, diagonal or antidiagonal bonds and uses row-major colour introduction. The 9-class exact-budget transfer counts labelled colourings. For n >= 2, KingTwoGrid.labelled_eq_twentyFour divides by 24; three occurring colours suffice for the free permutation action. The recurrence holds for every n >= 9, including the threshold.

**Theorem 1.2 (The width-3 closed form).**

$$\forall (n: \operatorname{Nat}), ((3 \le n) \Rightarrow ((8) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(n, 3\right)\right)) = (((2) \cdot ((1732) + ((117) \cdot (\operatorname{HPow}.\operatorname{hPow}\left(2, n\right))))) + ((((279) \cdot (\operatorname{HPow}.\operatorname{hPow}\left(2, n\right))) - (4084)) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(n\right)))) + ((((9) \cdot (\operatorname{HPow}.\operatorname{hPow}\left(2, n\right))) + (484)) \cdot (\operatorname{HPow}.\operatorname{hPow}\left(\operatorname{Int}.\operatorname{ofNat}\left(n\right), 2\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.closed_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

For every n >= 3, eight times the literal orbit count equals the displayed polynomial-exponential expression. The recurrence and the six values T(3,3)=598, T(4,3)=2347, T(5,3)=6809, T(6,3)=17404, T(7,3)=41872 and T(8,3)=97565 determine the solution by Mathlib LinearRecurrence.eq_iff_eqOn_range_order.

The nine-row forward table satisfies W(8)=-8W(2)+36W(3)-66W(4)+63W(5)-33W(6)+9W(7). DefectTransfer.forward_shift propagates this integer relation to every later height. The GridBridge identifies the row-list cost with the literal grid edge count. These are finite combinatorial states of the four-state Potts antiferromagnet at exactly two unsatisfied bonds; no empirical physical claim is asserted.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.closed_form`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip](../../../Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229536Strip](../CrossedStripDefects/HardinA229536Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/CrossedStripDefects/HardinA229632Strip](../CrossedStripDefects/HardinA229632Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid](KingTwoGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/GridBridge](TwoDefectStrips/GridBridge.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Certificate](TwoDefectStrips/Width3/Certificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Data](TwoDefectStrips/Width3/Data.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width3/Forward](TwoDefectStrips/Width3/Forward.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/Topology/QuandleMarkovColoring](../../../Topology/QuandleMarkovColoring.md)
