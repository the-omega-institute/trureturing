# Rational pure extensions on two Fibonacci words

## Abstract

A rational norm criterion for pure Fibonacci marginal extensions on two words.

**Theorem 1.1 (The rational norm criterion).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension.rational_pure_coupling_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension.rational_pure_coupling_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prescribe both edge marginals to be diagonal with entries 0, b, and 1 minus b in the order vacuum, occupied middle, occupied endpoint. For a given middle weight b and undetected coupling z, a trace-one pure extension with rational real and imaginary parts in every density matrix entry exists exactly when b and both coordinates of z are rational and |z|² = b(1 − b). For rational b, existence is thus equivalent to writing b(1 − b) as a sum of two rational squares.

The zero vacuum entries force the pure state to be supported on 010 and 101. Their weights are b and 1 minus b, and their coupling z satisfies |z|² = b(1 − b). Conversely, for b positive, let the two amplitudes be the positive square root of b and the conjugate of z divided by that root. The resulting matrix has the prescribed diagonal and entries z and its conjugate off the diagonal. For b zero, the state occupies only 101.

At b equal to one quarter, taking z equal to √3 / 4 gives a pure extension. Rational real and imaginary parts would express three as a sum of two rational squares. Clearing denominators gives a sum of two integer squares with odd three-adic valuation, which is impossible. The diagonal mixture of the two words gives a rational mixed extension.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension.rational_pure_coupling_iff`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension](FibMarginalExtension.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
