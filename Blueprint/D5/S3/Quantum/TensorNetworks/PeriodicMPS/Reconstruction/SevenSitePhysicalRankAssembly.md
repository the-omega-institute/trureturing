# A nonvanishing slice minor gives full rank of the graph readout

## Abstract

A nonvanishing slice minor gives full rank of the graph readout

**Theorem 1.1 (A nonvanishing slice minor gives full rank of the graph readout).**

Lean statement: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankAssembly.injective_fderiv_graphReadout`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankAssembly.injective_fderiv_graphReadout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At an ordinary seven-site chart point, assume its aligned mixed coordinate is nonzero. If a selected critical minor evaluated on the corresponding real slice is nonzero, the real derivative of the nine-component graph readout is injective.

The slice calculation relates the five coordinate columns, three rotation columns and radial column of the raw rows to the differential of the normalized marginal. The rank criterion is transported from the aligned slice to the original ordinary point.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankAssembly.injective_fderiv_graphReadout`
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteGraphReadout](SevenSiteGraphReadout.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSitePhysicalRankBridge](SevenSitePhysicalRankBridge.md)
