# Constant signed fibres

## Abstract

Each complementary-pair row has independent signed lifts.

**Theorem 1.1 (Weighted sum over signed lifts).**

$$\forall (k: \operatorname{Nat}), (\forall (w: (\operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(4\right)) \to \operatorname{Int}), (\sum_{(c: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(8\right))} (w\left((\operatorname{HardinA233196Strip}.\operatorname{beta} \circ c)\right)) = ((2: \operatorname{Int})^{k}) \cdot (\sum_{(r: \operatorname{Fin}\left(k\right) \to \operatorname{Fin}\left(4\right))} (w\left(r\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres.sum_beta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229750: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229750>.

*Commentary.*

For every natural width k, each function r from Fin k to Fin 4 has exactly 2^k preimages under pointwise beta. The scalar count is two for each of the four complementary colour pairs. Fintype.card_piFinset multiplies these independent choices. Finset.sum_fiberwise then groups any integer weight by its raw boundary. In particular the factors are eight at width three and sixteen at width four. No row-legality assumption is needed for the fibre count.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/SignedFibres.sum_beta`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](../../../../Combinatorics/TraceAvoidingArrays/HardinA233196Strip.md)
