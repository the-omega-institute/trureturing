# Coordinate translation to adjacent Hamming layers

## Abstract

Coordinate translation to adjacent Hamming layers

**Theorem 1.1 (One cube translation places the component on two layers).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers.exists_translate_adjacent_layers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers.exists_translate_adjacent_layers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When every direction has double fibres of just one transverse parity, a single XOR translation turns their parity choices into a common direction of weight increase. The difference between Hamming weight and the original parity bit is constant along each edge and therefore throughout the component. https://arxiv.org/html/2610.09483v1#Thmproblem2

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PureParityLayers.exists_translate_adjacent_layers`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CrossWitnessTotal](Q9CrossWitnessTotal.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity](Q9OccupiedFibreParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/WeightLayerParity](../SixtySixPointSupport/WeightLayerParity.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9ParityOverlap](../Translation/Q9ParityOverlap.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity](../Translation/Q9TranslationAperiodicity.md)
