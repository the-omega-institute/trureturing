# Passive Sector-Pair Bound

## Abstract

A passive correlated sector test bounds the overlap of every pair of actual local dilations.

**Theorem 1.1 (Spectral prefix bound for two sectors).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorPassivePair.sector_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorPassivePair.sector_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two isometric local dilations act on the same encoded source sector amplitude. Contracting their joint output against the flat target basis gives an environment matrix Z(s) for each sector s. For every sector pair s,t, the real Frobenius inner product of Z(s) and Z(t) is at most the Gram overlap of the two residual spectra.

The proof controls every singular-value prefix of Z(s) by the corresponding residual-spectrum prefix. It combines the rectangular variational bound with the source dilation's isometry and a trace majorization estimate. The same actual pair of dilations is used throughout; the result does not optimize the two sectors separately.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorPassivePair.sector_pair`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](../../Observer/Hilbert/FiniteMoorePenroseInverse.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](FiniteSectorChannelModel.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational](FiniteSectorRectangularVariational.md)
