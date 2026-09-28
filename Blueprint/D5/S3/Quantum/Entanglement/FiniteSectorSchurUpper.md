# Schur Channel Upper Bound

## Abstract

The physical Schur channel has diamond error bounded by the attained spectral minimum.

**Theorem 1.1 (Diamond upper bound from residual spectra).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.schur_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.schur_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual-overlap kernel is positive semidefinite, has diagonal one, and has entries at most one. A probability weight attains its minimum quadratic form on the nonempty finite sector simplex.

For every actual channel whose action on all logical matrices is the target encoding after Schur multiplication by this kernel, the unhalved diamond distance to the target encoding is at most twice one minus the spectral minimum. A pure correlated reference reduces the trace difference to a rank-one positive matrix minus a positive matrix of equal trace. Its positive spectral part has rank at most one. The existing finite diamond-distance theorem supplies the pure-reference reduction for arbitrary joint density inputs.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.schur_upper`
- Dependency: [D5/S3/Observer/Hilbert/FiniteMoorePenroseInverse](../../Observer/Hilbert/FiniteMoorePenroseInverse.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorChannelModel](FiniteSectorChannelModel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
