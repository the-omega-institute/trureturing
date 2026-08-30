# Perfect Record Mirror Readout

## Abstract

A perfect unread record erases every mirror observable with no record-diagonal block.

**Theorem 1.1 (Perfect recording forces zero mirror expectation).**

$$\begin{gathered}\forall n, K, \operatorname{Fintype}\left(n\right), \operatorname{DecidableEq}\left(n\right), \operatorname{Fintype}\left(K\right)\\{}P: K \to M_{n}(\mathbb{C}),\\{}\operatorname{IsRecordMeasurement}\left(P\right) \Rightarrow\\{}\forall rho: M_{n}(\mathbb{C}), \forall J: M_{n}(\mathbb{C}), (\forall k: K, P_{k} J P_{k} = 0) \Rightarrow \operatorname{Tr}\left(E_{P}(rho)J\right) = 0 \land \operatorname{Tr}\left(E_{P}(rho)\right) = \operatorname{Tr}\left(rho\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout.perfect_record_mirror_readout_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite complete family of pairwise orthogonal self-adjoint complex matrix projections, the unread map is the sum of the diagonal compressions P_k rho P_k.

If an observable has zero diagonal block P_k J P_k for every record value, cyclicity of the matrix trace makes its pairing with the unread state vanish. The same statement also records that the unread map preserves the trace of rho.

The companion incompatibility corollary states that a nonzero unread readout must retain a nonzero record-diagonal block; qualitative observer-ontology alternatives in the source are not additional mathematical clauses.

## References

- Truth anchor: `D5/S3/Observer/Conditioning/PerfectRecordMirrorReadout.perfect_record_mirror_readout_zero`
- Dependency: [D5/S3/Observer/Conditioning](../Conditioning.md)
