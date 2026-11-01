# The symmetric slice is algebraically sharp

## Abstract

Exact identities on the symmetric sharp slice.

On the slice o=r, A=B=h and zeta=0, write t=xi^2. The asymmetric remainder becomes 2(r^2-1)t+t^2. The square-root radius simplifies to (r+1)(1+2h-r). The result is an exact algebraic identity for every r>1 and h>1; it does not assert a global CFMP realization.

**Theorem 1.1 (Exact remainder and radius).**

$$\forall r \in Real, h \in Real, xi \in Real,\; \left(1 < r \land 1 < h\right) \Rightarrow \left(Xi\left(r, r, h, h, xi, 0\right) = (((2\cdot ((r^2)-1))\cdot (xi^2))+((xi^2)^2)) \land (sqrt\left(((((r^2)-1)^2)+(L\left(r, r, h, h\right)\cdot M\left(r, r, h, h\right)))\right)-((r^2)-1)) = ((r+1)\cdot ((1+(2\cdot h))-r))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SharpSymmetricSlice.sharp_symmetric_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first conjunct evaluates the full four-term asymmetry polynomial after the symmetric substitutions. The second conjunct evaluates the positive square root using r>1 and h>1.

This is a local six-coordinate identity. It supplies the sharp slice calculation used in the surrounding stability argument, without claiming that the averaged slice is a global zero-curvature solution.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SharpSymmetricSlice.sharp_symmetric_slice`
- Dependency: [D5/S3/Geometry/Hyperideal/SixIndependentLengthStability](SixIndependentLengthStability.md)
