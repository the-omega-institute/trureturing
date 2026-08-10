# Propagation Identity

## Abstract

A crossing slot propagates three square-root-of-three legs and reduces its discriminant to a Pythagorean spectral line.

**Theorem 1.1 (Three propagated legs and spectral line).**

$$\forall A,u,D\in\mathbb{R},\ A\neq0 \land D=3A^2+u^2 \Rightarrow (D-3A^2=u^2 \land D-3(\frac{u-A}{2})^2=(\frac{3A+u}{2})^2 \land D-3(\frac{u+A}{2})^2=(\frac{3A-u}{2})^2) \land \frac{\sqrt{D}}{\Vert A \Vert}=\sqrt{3+(\frac{u}{A})^2}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/PropagationLegs.propagation_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The represented values A, (u-A)/2, and (u+A)/2 are all square-root-of-three legs of the same crossing slot. Their respective companions are u, (3A+u)/2, and (3A-u)/2. The same theorem records the spectral reduction of the normalized discriminant square root, with the nonzero-base hypothesis making the quotient well-defined.

## References

- Truth anchor: `D5/S3/PrimeForms/PropagationLegs.propagation_identity`
