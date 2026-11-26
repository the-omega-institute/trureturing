# Literal matching switches merge precisely the intended boundary components

## Abstract

Literal matching switches merge precisely the intended boundary components.

**Theorem 1.1 (Literal matching switches merge precisely the intended boundary components).**

$$\operatorname{ExactOperationalStateEquivalence}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonFlagGeometry.match_switch_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Before a switch, deleting one edge of the second matching in either old cycle cannot split that cycle: a proposed cut would be paired by the first involution, but paired by the second involution except at exactly one marked point. The opposite parity is impossible. This parity fact, together with the genuine dihedral cycle coordinates, is a live input to the marked ribbon chart construction.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/MarkedRibbonFlagGeometry.match_switch_join`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/RibbonCohomologyRank](../../../Combinatorics/PerfectMatchings/RibbonCohomologyRank.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/SignedBouquetBoundary](../../../Combinatorics/PerfectMatchings/SignedBouquetBoundary.md)
- Dependency: [D5/S3/Quantum/Entanglement/StabilizerMultiEntropy/SignedBouquetMomentReconstruction](SignedBouquetMomentReconstruction.md)
