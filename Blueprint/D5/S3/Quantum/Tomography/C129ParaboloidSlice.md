# C129 Paraboloid Slice

## Abstract

The positive two-by-two Gram region has a nonnegative Schur residual and paraboloid coordinates.

**Theorem 1.1 (Positive two-by-two blocks and the zero-diagonal boundary).**

$$\forall p, q, b \Rightarrow ((0 < p \Rightarrow ((\operatorname{twoByTwoPositive}(p, q, b) \iff 0 \leq \operatorname{residual}(p, q, b)) \land q = \operatorname{xCoord}(p, b)^{2} + \operatorname{yCoord}(p, b)^{2} + \operatorname{residual}(p, q, b))) \land (p = 0 \Rightarrow \operatorname{twoByTwoPositive}(p, q, b) \Rightarrow (b = 0 \land 0 \leq q)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/C129ParaboloidSlice.paraboloid_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real p and q and a complex cross term b, twoByTwoPositive records nonnegative diagonal entries and the determinant inequality for the Hermitian two-by-two block. When p is positive, the block is positive exactly when the Schur residual q - normSq(b)/p is nonnegative.

The normalized real and imaginary cross-term coordinates are Re(b)/sqrt(p) and Im(b)/sqrt(p). Their squared coordinates together with the Schur residual recover q, so the allowed region is the paraboloid and its upper region. At p = 0, positivity forces b = 0 while q remains nonnegative.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/C129ParaboloidSlice.paraboloid_slice`
