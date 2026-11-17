# Auric contact coefficient identities

## Abstract

The Auric scalar contact coefficients admit explicit factorizations at the cost centre, with nonvanishing central coefficients.

**Theorem 1.1 (Explicit coefficient identities at t = 1/4).**

$$\forall x, y, t \in \mathbb{R},\ x \ne 0 \land 1<y^{2} \Rightarrow (\operatorname{fOne}(x, y)=\operatorname{fOneFactored}(x, y) \land \operatorname{gZero}(x, y)=\operatorname{gZeroFactored}(x, y) \land \operatorname{fCenter}(x, y)=\operatorname{fCenterClosed}(x, y) \land \operatorname{gCenter}(x, y)=\operatorname{gCenterClosed}(x, y) \land \operatorname{fCenter}(x, y) \ne 0 \land \operatorname{gCenter}(x, y) \ne 0 \land \operatorname{g}(x, y, t)=\operatorname{gClosed}(x, y, t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/AuricContactCoefficient.lemma_46_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real coordinates satisfy x nonzero and y squared greater than one, and ell is the complex coordinate x + y I. The theorem expands the coefficients from the source-aligned scalar graph: fOne and gZero are the factored forms of the derivative and zero-parameter coefficients.

At the cost centre t = 1/4, the central coefficient fCenter has real part (x-4)/2 and imaginary part -(5 y squared + 6 (x-1) squared)/(2y). The central g coefficient is (ell-2)(2 + 3 I (x+1)/(2y)); both are nonzero because y squared is greater than one.

For arbitrary t, zeta is 4t and beta is 3(1+zeta), and g equals -(2-ell)/4 times the displayed real-affine bracket. This is the algebraic identity layer of Lemma 46.3 only; it does not assert the contact equations, the root polynomial, or the global cost lower bounds from the surrounding theory.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/AuricContactCoefficient.lemma_46_3`
