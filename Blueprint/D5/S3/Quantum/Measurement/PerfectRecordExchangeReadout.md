# Perfect Record Exchange Readout

## Abstract

A perfect copied-address record eliminates the exchange readout after the record is discarded.

**Theorem 1.1 (Perfect recording eliminates the unread exchange readout).**

$$\begin{gathered}\forall \rho: QubitMatrix,\\{}jointState := \operatorname{controlledRecordJointState}\left(copiedAddressRecord, \rho\right);\\{}unreadMarginal := \operatorname{traceEnvironment}\left(jointState\right);\\{}\operatorname{Tr}\left(unreadMarginal \cdot qubitX\right) = 0 \land\\{}\neg(\operatorname{Tr}\left(unreadMarginal \cdot qubitX\right) \neq 0) \land\\{}(\forall i, j: \operatorname{Fin}\left(2\right), i \neq j \land \rho_{ij} \neq 0 \Rightarrow\\{}jointState_{(i,i),(j,j)} \neq 0 \land unreadMarginal_{ij} = 0) \land\\{}(\forall readout: QubitMatrix \to \mathbb{C}, readout(unreadMarginal) \neq 0 \Rightarrow\\{}readout \neq (\sigma: QubitMatrix \mapsto \operatorname{Tr}\left(\sigma \cdot qubitX\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/PerfectRecordExchangeReadout.perfect_record_exchange_readout_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input rho is an arbitrary complex matrix on two addresses; no positivity, normalization, or diagonal hypothesis is required. The joint state is constructed with the repository's canonical copied-address record, and the unread marginal is constructed by tracing that record out.

The copied-record marginal has zero off-diagonal entries. Since qubitX has only off-diagonal entries, their trace pairing is zero. Thus a nonzero readout function cannot be the same function as this exchange pairing on the unread interface.

For every distinct address pair, nonzero input coherence remains nonzero in the matched system-record entry of the controlled joint state while the corresponding unread marginal entry is zero. This exposes the joint-record alternative using the same construction as the vanishing readout.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/PerfectRecordExchangeReadout.perfect_record_exchange_readout_vanishes`
- Dependency: [D5/S3/Observer/MeasurementMarginal](../../Observer/MeasurementMarginal.md)
