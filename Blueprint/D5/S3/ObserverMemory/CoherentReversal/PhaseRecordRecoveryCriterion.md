# Phase-Record Recovery Criterion

## Abstract

Finite phase records recover exactly at unit overlap, while strict overlap contraction leaves a squared residual factor.

**Theorem 1.1 (Finite phase-record recovery and its two obstructions).**

$$\begin{gathered}\forall Copy: \operatorname{Type}, [\operatorname{Fintype}\left(Copy\right)], [\operatorname{DecidableEq}\left(Copy\right)],\\{}R: Copy \to \operatorname{EnvironmentRecord}, \rho: \operatorname{QubitMatrix}, i: \operatorname{Fin}\left(2\right), j: \operatorname{Fin}\left(2\right),\\{}((\forall k, \lvert \operatorname{recordOverlap}\left(R(k), i, j\right) \rvert = 1) \Rightarrow \operatorname{multiRecordChannel}\left(\operatorname{reverseOn}\left(univ, R\right), \operatorname{multiRecordChannel}\left(R, \rho\right)\right)(i)(j) = \rho(i)(j)) \land\\{}((\exists k, \lvert \operatorname{recordOverlap}\left(R(k), i, j\right) \rvert < 1) \Rightarrow \exists k,\\{}\lvert \operatorname{recordOverlap}\left(R(k), i, j\right) \rvert < 1 \land \lvert \operatorname{recordOverlap}\left(R(k), i, j\right) \rvert^{2} < 1 \land\\{}\operatorname{recordChannel}\left(\operatorname{reverseRecord}\left(R(k)\right), \operatorname{recordChannel}\left(R(k), \rho\right)\right)(i)(j) = \lvert \operatorname{recordOverlap}\left(R(k), i, j\right) \rvert^{2} \rho(i)(j) \land\\{}(\rho(i)(j) \neq 0 \Rightarrow \operatorname{recordChannel}\left(\operatorname{reverseRecord}\left(R(k)\right), \operatorname{recordChannel}\left(R(k), \rho\right)\right)(i)(j) \neq \rho(i)(j))) \land\\{}(\forall k, (\forall l, l \neq k \Rightarrow \lvert \operatorname{recordOverlap}\left(R(l), i, j\right) \rvert = 1) \Rightarrow \operatorname{recordOverlap}\left(R(k), i, j\right) \neq 1 \Rightarrow \rho(i)(j) \neq 0 \Rightarrow\\{}\operatorname{reverseChannelOn}\left(\operatorname{erase}\left(univ, k\right), R, \operatorname{multiRecordChannel}\left(R, \rho\right)\right)(i)(j) \neq \rho(i)(j)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/CoherentReversal/PhaseRecordRecoveryCriterion.phase_record_recovery_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite family of canonical environment records act on one selected matrix entry. If every record overlap has norm one, the imported all-copy reversal theorem restores that entry after every record is amplitude-conjugated.

If some overlap has norm strictly below one, the same record followed by its conjugate record channel multiplies the entry by the squared overlap norm, which is still strictly below one. Consequently a nonzero selected entry is not restored.

Finally, if one overlap unequal to one is left unreversed while every other overlap has norm one, the imported surviving-copy theorem shows that a nonzero selected entry is not restored. The statement uses the frozen record, overlap, channel, and reversal operations throughout; it introduces no replacement model.

## References

- Truth anchor: `D5/S3/ObserverMemory/CoherentReversal/PhaseRecordRecoveryCriterion.phase_record_recovery_criterion`
- Dependency: [D5/S3/ObserverMemory/JointCoherentReversal](../JointCoherentReversal.md)
