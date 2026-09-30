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


**Theorem 1.2 (Simplex variational domination).**

Lean statement: `D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.simplex_quadratic_dominates_weighted_complex_form`

*Formalization status.* Lean declaration added on branch `lane/theory/rt-variational-20260930`; focused kernel and CI checks are pending. ∎

*Source.* Repository-derived.

*Commentary.*

For every nonempty finite sector type and entrywise nonnegative real matrix \(A\), one simplex point \(r\) simultaneously maximizes \(Q_A(w)=\sum_{i,j}A_{ij}w_iw_j\) over the simplex and upper-bounds every weighted complex form
\[
R_A(p,x)=\sum_{i,j}\sqrt{p_i}\sqrt{p_j}A_{ij}\operatorname{Re}(\overline{x_i}x_j)
\]
when \(p\) is a simplex point and \(\sum_i\lVert x_i\rVert^2=1\). The proof takes \(y_i=\sqrt{p_i}\lVert x_i\rVert\), uses Cauchy--Schwarz to show \(\sum_i y_i\le1\), fills the deficit at one coordinate to obtain a simplex point \(w\ge y\), and then applies the phase bound \(\operatorname{Re}(\overline{x_i}x_j)\le\lVert x_i\rVert\lVert x_j\rVert\). This is the variational step needed to control arbitrary passive references in the finite-sector Schur estimate; it does not assert a continuum gravitational RT identity.
