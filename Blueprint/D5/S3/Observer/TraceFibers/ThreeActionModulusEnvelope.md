# Three Action Modulus Envelope

## Abstract

The three-action Fibonacci fiber has seven matrix coefficient shapes, with two non-dominated shapes whose scalar envelopes cross at one tolerance.

**Theorem 1.1 (Three-action scalar envelope).**

$$\begin{aligned}k \ge 1, 0 < h < 1, x = {k+h}\cdot r\\tauStar = 2\cdot r\cdot h, dStar = r\cdot h\\TS = {k+2}\cdot x, TA = 2\cdot {k+1}\cdot x\\phiA - phiS = d\cdot {\frac{d-r\cdot h}{r}}\\tauStar < TS < TA\\d = dStar \Rightarrow phiA = phiS = tauStar\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For words of length at most three in the advance and exchange actions, the pair consisting of the diagonal difference and lower-left entry has exactly seven possible values. The positive-entry injective shapes are (1,1), (2,1), and (2,2); the latter two are represented by MJM and MMM, while (1,1) is represented by the shorter compatible words.

Writing d for a source spacing, the two distinguished scalar separation functions are phi_S(d)=(2-h)d+d^2/r and phi_A(d)=(2-2h)d+2d^2/r. Their difference is d(d/r-h), so their common spacing is rh and their common tolerance is 2rh.

The endpoint values of the two quadratic separation functions are ordered by k and h, while the common spacing is rh. The inverse-envelope root is supplied by the fixed-fiber modulus interface.

## References

- Truth anchor: `D5/S3/Observer/TraceFibers/ThreeActionModulusEnvelope.three_action_modulus_envelope`
- Dependency: [D5/S3/Observer/TraceFibers/FixedFiberPairModulus](FixedFiberPairModulus.md)
