# Perfect Record Mirror Readout

## Abstract

Discarding a perfect two-address record erases the fixed mirror-swap expectation.

**Theorem 1.1 (Perfect recording forces zero mirror expectation).**

$$\begin{gathered}\forall rho: M_{\operatorname{Fin}\left(2\right)}(\mathbb{C}), \operatorname{Tr}\left(\operatorname{unreadState}\left(addressProjection, rho\right) \cdot qubitX\right) = 0.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout.perfect_record_mirror_readout_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state rho is an arbitrary complex matrix on the canonical two-address carrier. The standard address projectors define the unread map, and qubitX is the fixed observable that exchanges the two addresses.

Each address compression has zero pairing with the off-diagonal swap. Cyclicity and linearity of the matrix trace therefore make the pairing with unreadState addressProjection rho vanish.

This declaration owns only the displayed zero-expectation clause. The ledger atom remains guarded because its later classical-label, five-way-alternative, and observer-ontology clauses have no current public carrier.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout.perfect_record_mirror_readout_zero`
- Dependency: [D5/S3/Observer/Conditioning](../Conditioning.md)
- Dependency: [D5/S3/Observer/MeasurementMarginal](../MeasurementMarginal.md)
