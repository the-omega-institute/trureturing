# Backward Shift Operator

## Abstract

The frozen coefficient pullback is a contraction adjoint with divisibility-truncated basis action.

**Theorem 1.1 (The backward shift is a contraction).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \Vert \operatorname{backwardShiftCLM}(u)\Vert \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftOperator.backward_shift_operator_norm_le_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime-axis address u, backwardShiftCLM is the frozen backwardShift coefficient pullback bundled as a continuous linear map on ZetaHilbertSpace. Its operator norm is at most one because right multiplication of encoded addresses is injective, so the pulled-back square-norm sum is bounded by the original sum.

**Theorem 1.2 (The backward shift is the translation adjoint).**

$$\forall u\in \operatorname{PrimeAxisTable},\ \forall x, y\in \operatorname{ZetaHilbertSpace},\ \operatorname{sourcePairing}(\operatorname{backwardShiftCLM}(u)(x), y) = \operatorname{sourcePairing}(x, \operatorname{forwardTranslationCLM}(u)(y))$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftOperator.backward_shift_sourcePairing_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all Hilbert vectors x and y, the source pairing of the backward shift of x with y equals the source pairing of x with the forward translation of y. No forward shift was frozen in the repository, so forwardTranslationCLM is constructed here independently by extending coefficients by zero off the injective multiplicative-translation image. The identity follows by reindexing that zero extension.

**Theorem 1.3 (Basis kets subtract exactly on divisible addresses).**

$$\forall u, b\in \operatorname{PrimeAxisTable},\ \operatorname{backwardShiftCLM}(u)(\operatorname{ket}(b)) = \begin{cases}\operatorname{ket}(\operatorname{normalizedTableSub}(b, u)),&\operatorname{primeAxisEncoding}(u) \mid \operatorname{primeAxisEncoding}(b)\\0,&\neg \operatorname{primeAxisEncoding}(u) \mid \operatorname{primeAxisEncoding}(b)\end{cases}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ShiftOperators/BackwardShiftOperator.backward_shift_basis_subtraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here ket(b) denotes the normalized single-support vector lp.single 2 b 1. If the positive-natural encoding of u divides that of b, the backward shift sends ket(b) to ket(normalizedTableSub b u); if not, it sends the ket to zero. The subtraction is PNat.divExact transported through the frozen primeAxisEncoding, and normalizedTableSub_add_cancel proves the divisible branch rather than installing it by definition.

## References

- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftOperator.backward_shift_basis_subtraction`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftOperator.backward_shift_operator_norm_le_one`
- Truth anchor: `D5/S3/Zeros/ShiftOperators/BackwardShiftOperator.backward_shift_sourcePairing_adjoint`
- Dependency: [D5/S3/Weil/SpectralHilbert](../../Weil/SpectralHilbert.md)
- Dependency: [D5/S3/Zeros/SpectralShift](../SpectralShift.md)
