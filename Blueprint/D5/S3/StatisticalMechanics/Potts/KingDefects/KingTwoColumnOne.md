# Two-defect paths

## Abstract

Canonical four-colour paths with exactly two equal adjacent pairs.

The prefix and adjacent-edge reconstructions, finite state transition counts and count-to-matrix induction establish the domain counting correspondence. The recurrence consumes this content together with the arithmetic matrix certificate.

**Theorem 1.1 (The width-one six-term recurrence).**

$$\forall (n: \operatorname{Nat}), ((10 \le n) \Rightarrow (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(n, 1\right)\right) = ((((((12) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 1\right), 1\right)\right))) - ((57) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 2\right), 1\right)\right)))) + ((136) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 3\right), 1\right)\right)))) - ((171) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 4\right), 1\right)\right)))) + ((108) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 5\right), 1\right)\right)))) - ((27) \cdot (\operatorname{Int}.\operatorname{ofNat}\left(\operatorname{KingTwoGrid}.\operatorname{T}\left(\operatorname{Nat}.\operatorname{sub}\left(n, 6\right), 1\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229755: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229755>.

*Commentary.*

A one-column king array is a path. Its canonical word starts with colour zero. After this first cell, a state records the number m of introduced colours and the remaining defect budget d, where 1 <= m <= 4 and 0 <= d <= 2. There are m-1 existing colours different from the preceding colour, one equal colour if a defect remains, and one new colour when m < 4. These transitions count two-colour words as well as words using three or four colours.

The integer transfer has twelve states indexed by 3(m-1)+d. Its terminal vector is the indicator of d=0. A table of type Fin 10 -> Fin 12 -> Int records ten backward iterates. The certificate pins its initial vector, each successive multiplication by the transposed transfer, and the order-six relation from iterates 3 through 9. DefectTransfer.forward_shift propagates that relation to every later height. The row-major canonical-word equivalence identifies these counts with the literal grid count.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../../../Combinatorics/TraceAvoidingArrays/HardinA233196Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingGrid](KingGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath](KingPath.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid](KingTwoGrid.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../StripDefects/DefectTransfer.md)
