# Constant signed fibres

## Abstract

Each complementary-pair row has independent signed lifts.

**Theorem 1.1 (Weighted sum over signed lifts).**

$$\forall (k: \operatorname{Nat}), (\forall (w: (\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(4\right)) \to \operatorname{Int}), (\sum_{(c: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(8\right))} (w\left((\operatorname{HardinA233196Strip}.\operatorname{beta} \circ c)\right)) = ((2: \operatorname{Int})^{k}) \cdot (\sum_{(r: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(4\right))} (w\left(r\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres.sum_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

The complementary-colour equivalence identifies a lifted row with a pair (r,b), where r maps Fin k to Fin 4 and b maps Fin k to Bool. Its first coordinate is pointwise beta. Reindexing the sum by this equivalence makes the weight independent of b. There are 2^k Boolean rows, so summing over b gives the stated factor. In particular the factors are eight at width three and sixteen at width four. No row-legality assumption is needed.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres.sum_beta`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233166KingStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233196Strip.md)
