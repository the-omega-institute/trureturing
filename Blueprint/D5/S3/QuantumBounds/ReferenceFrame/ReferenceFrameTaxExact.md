# Exact Finite Reference-Frame Tax

## Abstract

The finite exchange model has an exact fidelity bridge, sharp tax, restricted flat tax, and paired top eigenspace.

**Theorem 1.1 (The finite reference-frame tax is exact).**

Lean statement: `D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact`

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The declaration packages the concrete exchange permutation, its conservation law, the finite Kraus representation, and both exact fidelity forms. It then applies the frozen sharp quadratic bound, the sine identity, the flat identity for ladders of length at least two, and the imported paired top-eigenspace characterization.

The lower bound on the ladder length is explicit because the one-level flat calculation has tax one rather than the displayed three-halves formula.

## References

- Truth anchor: `D5/S3/QuantumBounds/ReferenceFrame/ReferenceFrameTaxExact.reference_frame_tax_exact`
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/ChannelFidelityBridge](ChannelFidelityBridge.md)
- Dependency: [D5/S3/QuantumBounds/ReferenceFrame/TopEigenspace](TopEigenspace.md)
